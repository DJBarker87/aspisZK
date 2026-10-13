//! UNPROVED COST PROBE. Dense native self-consistency evaluator.
//! Uses E arithmetic, literal 1024-entry rows and original circle folding.
use aspis_core::r0::CodeField;
use alloc::{vec,vec::Vec};
use aspis_core::{HashFn,field::{WideExact as E,QM31 as K,M31},r0::{self,domain::{FibreIndex,Point},merkle},r0_transcript as sample};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
use crate::{r1_wire as wire,trace,transport::Variant,verifier::{Error,View,INITIAL_QUERY_BYTES}};
fn powers(x:E,n:usize)->Vec<E> {let mut a=E::ONE;(0..n).map(|_|{let b=a;a=a.mul(x);b}).collect()}
fn value(bytes:&[u8],i:usize)->E {E::from_le_bytes(&bytes[32*i..32*i+32]).unwrap()}
fn eval(poly:&[E],x:E)->E {poly.iter().rev().fold(E::ZERO,|v,&c|v.mul(x).add(c))}
fn dot(a:&[E],b:&[E])->E {a.iter().zip(b).fold(E::ZERO,|v,(&a,&b)|v.add(a.mul(b)))}
fn semantic_block(hash:HashFn,state:&mut[u8;32],row:u8,record:&[u8])->[u8;32] {
    let absorbed=hash(&[state,&[0,0xa0+row],record]);let block=hash(&[&absorbed,&[1]]);*state=hash(&[&absorbed,&[2]]);block
}
fn absorb(hash:HashFn,state:&mut[u8;32],row:u8,b:&[u8]) {*state=hash(&[state,&[0,0xa0+row],&(b.len()as u32).to_le_bytes(),b]);}
fn scalar(hash:HashFn,state:&mut[u8;32],row:u8,b:&[u8],nonzero:bool)->E {
    absorb(hash,state,row,b);let block=hash(&[state,&[1]]);*state=hash(&[state,&[2]]);
    let x=if nonzero {sample::gamma_sample(&block)}else{sample::ordinary_sample(&block)};trace::value(4,row as usize,x);x
}
fn queries(hash:HashFn,state:&mut[u8;32],row:u8,b:&[u8])->Result<[u32;22],Error> {
    absorb(hash,state,row,b);let mut out=[0;22];let mut count=0;let mut draws=0;
    'blocks: for _ in 0..8 {
        let block=hash(&[state,&[1]]);*state=hash(&[state,&[2]]);
        for bytes in block.chunks_exact(4) {
            if count==22||draws==64 {break 'blocks;}
            draws+=1;let q=u32::from_le_bytes(bytes.try_into().unwrap())&((1<<18)-1);
            if !out[..count].contains(&q) {out[count]=q;count+=1;}
        }
    }
    if count!=22 {return Err(Error::Transcript);}
    for (i,&u) in out.iter().enumerate(){trace::value(5,i,E::from_m31(M31(u)));}Ok(out)
}
fn row(v:Variant,j:usize)->usize {
    if v==Variant::D {return r0::transport::COEFFICIENT_TO_ROW[j]as usize;}
    ((j&3)<<6)+(((j>>2)&3)<<8)+(((j>>4)&3)<<4)+((j>>6)&3)+(((j>>8)&3)<<2)
}
fn second_fold(alpha:E,u:usize,values:[E;4])->E {
    // Dense natural-basis interpolation, independent of the verifier's
    // specialized line transform. Four base-field abscissae are distinct.
    let mut matrix=[[E::ZERO;5];4];
    for s in 0..4 {let x=r0::domain::line_node::<E>(FibreIndex::new(u/4*4+s).unwrap());for j in 0..4 {matrix[s][j]=r0::basis::natural(j,x);}matrix[s][4]=values[s];}
    for j in 0..4 {
        let pivot=(j..4).find(|&i|matrix[i][j]!=E::ZERO).unwrap();matrix.swap(j,pivot);
        let inverse=matrix[j][j].try_inv().unwrap();for k in j..5 {matrix[j][k]=matrix[j][k].mul(inverse);}
        for i in 0..4 {if i!=j {let factor=matrix[i][j];for k in j..5 {matrix[i][k]=matrix[i][k].sub(factor.mul(matrix[j][k]));}}}
    }
    eval(&core::array::from_fn::<_,4,_>(|j|matrix[j][4]),alpha)
}
pub fn verify(public:Public<'_>,proof:&[u8],hash:HashFn)->Result<(),Error> {
    let v=View::parse(proof)?;let prefix=wire::Prefix::parse(v.semantic).map_err(|_|Error::Parse)?;
    let pb=public.public_bytes().map_err(|_|Error::Parse)?;
    let mut state=hash(&[wire::DOMAIN,&[0],&(pb.len()as u32).to_le_bytes(),&pb,prefix.c1_root]);
    let mut samples=[K::ZERO;25];let mut running=value(prefix.payload(14).unwrap(),0);
    for row in 0..25u8 {
        let block=semantic_block(hash,&mut state,row,prefix.record(row).unwrap());samples[row as usize]=sample::qm31_sample(&block);
        trace::value(0,row as usize,E::from_qm31(samples[row as usize]));
        if row>=15 {
            let poly:Vec<E>=(0..28).map(|i|value(prefix.payload(row).unwrap(),i)).collect();
            let boundary=poly.iter().copied().fold(poly[0],E::add);
            let next=eval(&poly,E::from_qm31(samples[row as usize]));
            for (j,x) in [running,boundary,next].into_iter().enumerate(){trace::value(1,3*(row as usize-15)+j,x);}
            if boundary!=running {return Err(Error::Semantic);}running=next;
        }
    }
    let challenges=aspis_core::state_only_prefix::r0::Challenges{lambda:samples[0],chi:samples[1],theta:samples[2],zc:core::array::from_fn(|j|samples[3+j]),mu:samples[13],eta:samples[14]};
    let alpha: [K;10]=core::array::from_fn(|j|samples[15+j]);
    let claims=core::array::from_fn(|p|core::array::from_fn(|l|value(prefix.payload(25).unwrap(),p*29+l)));
    let extra:Vec<E>=(0..29).map(|l|value(prefix.payload(25).unwrap(),87+l)).collect();
    let terminal=public.terminal(&claims,&alpha,&challenges).map_err(|_|Error::Semantic)?;
    let masked=aspis_core::state_only_hiding::r0::masked_terminal(&claims,&alpha,challenges.eta,terminal).add(extra[28]);
    trace::value(2,0,terminal);trace::value(2,1,masked);if running!=masked{return Err(Error::Semantic);}
    let b0=semantic_block(hash,&mut state,25,prefix.record(25).unwrap());let z0=sample::circle_sample(&b0,sample::CircleRow::First);
    let b1=semantic_block(hash,&mut state,26,prefix.record(26).unwrap());let z1=sample::circle_sample(&b1,sample::CircleRow::Second);
    if z0==z1{return Err(Error::Semantic);}let z=[z0,z1];
    for (i,x) in [z0.x,z0.y,z1.x,z1.y].into_iter().enumerate(){trace::value(3,i,E::from_qm31(x));}
    #[cfg(not(feature="private-leaf-salts"))]
    let transcript_domain: &[u8]=b"UNPROVED:R1:COST-PROBE:P2";
    #[cfg(feature="private-leaf-salts")]
    let transcript_domain: &[u8]=b"UNPROVED:R1:PRIVATE-SALTED:P3";
    state=hash(&[transcript_domain,&[v.variant.tag()],&state]);
    let gamma=scalar(hash,&mut state,27,v.y1,true);let kappa=scalar(hash,&mut state,28,&v.inactive.to_le_bytes(),false);
    let mut folding=vec![scalar(hash,&mut state,29,v.round0,false)];
    if v.variant.folds()==2 {let mut b=v.folded_root.unwrap().to_vec();b.extend_from_slice(v.round1);folding.push(scalar(hash,&mut state,30,&b,false));}
    let query_row=if v.variant.folds()==1 {30}else{31};let queries=queries(hash,&mut state,query_row,v.final_message)?;
    absorb(hash,&mut state,query_row+1,&[]);let block=hash(&[&state,&[1]]);state=hash(&[&state,&[2]]);
    let rho=E::from_qm31(sample::qm31_sample(&block));trace::value(4,(query_row+1) as usize,rho);let gp=powers(gamma,29);let kp=powers(kappa,7);
    let mut claims_batch=[E::ZERO;7];claims_batch[0]=v.inactive;
    for p in 0..3 {claims_batch[p+1]=dot(&gp,&claims[p]);}
    claims_batch[4]=dot(&gp,&extra);
    let endpoints:Vec<E>=(0..29).map(|l|value(prefix.payload(26).unwrap(),l)).collect();claims_batch[5]=dot(&gp,&endpoints);
    let endpoints:Vec<E>=(0..29).map(|l|value(v.y1,l)).collect();claims_batch[6]=dot(&gp,&endpoints);
    for (j,&x) in claims_batch.iter().enumerate(){trace::value(14,j,x);}let mut relation=dot(&kp,&claims_batch);trace::value(14,7,relation);
    let final_message:Vec<E>=(0..v.variant.final_len()).map(|j|value(v.final_message,j)).collect();
    let mut batch_weights=vec![E::ZERO;final_message.len()];let mut rhs=E::ZERO;let mut rho_power=E::ONE;
    let roots=[*prefix.c1_root,prefix.payload(2).unwrap().try_into().unwrap()];
    for (i,&u) in queries.iter().enumerate() {
        let q=v.query(i);
        #[cfg(not(feature = "private-leaf-salts"))]
        let path_start=608;
        #[cfg(feature = "private-leaf-salts")]
        let path_start=672;
        let paths=core::array::from_fn(|t|core::array::from_fn(|d|core::array::from_fn(|s|q[path_start+t*1344+d*224+s*32..path_start+t*1344+d*224+s*32+32].try_into().unwrap())));
        #[cfg(not(feature = "private-leaf-salts"))]
        let leaf=[merkle::leaf(hash,merkle::C1_TAG,&q[..480]),merkle::leaf(hash,merkle::C2_TAG,&q[480..608])];
        #[cfg(feature = "private-leaf-salts")]
        let leaf=[
            hash(&[&[0x10,merkle::C1_TAG],&q[..480],&q[608..640]]),
            hash(&[&[0x10,merkle::C2_TAG],&q[480..608],&q[640..672]]),
        ];
        if !merkle::verify_pair(hash,&roots,FibreIndex::new(u as usize).unwrap(),leaf,&paths){return Err(Error::Merkle);}
        let mut values=[E::ZERO;4];
        for s in 0..4 {
            for l in 0..29 {
                let x=if l<26 {E::from_m31(M31::from_le_bytes(q[s*120+l*4..s*120+l*4+4].try_into().unwrap()).unwrap())}
                    else if l==28 {E::from_qm31(K::from_le_bytes(&q[s*120+104..s*120+120]).unwrap())}
                    else {E::from_qm31(K::from_le_bytes(&q[480+s*32+(l-26)*16..480+s*32+(l-26)*16+16]).unwrap())};
                values[s]=values[s].add(gp[l].mul(x));
            }
            trace::value(9,4*i+s,values[s]);
        }
        let mut folded=r0::fold::fold_fibre(folding[0],FibreIndex::new(u as usize).unwrap(),values).unwrap();trace::value(10,2*i,folded);
        if v.variant.folds()==2 {
            let b=&q[INITIAL_QUERY_BYTES..];let values=core::array::from_fn(|s|value(b,s));
            #[cfg(not(feature = "private-leaf-salts"))]
            let (path_at,leaf)=(128,merkle::leaf(hash,0x72,&b[..128]));
            #[cfg(feature = "private-leaf-salts")]
            let (path_at,leaf)=(160,hash(&[&[0x10,0x72],&b[..128],&b[128..160]]));
            let path=core::array::from_fn(|d|core::array::from_fn(|s|b[path_at+d*224+s*32..path_at+d*224+s*32+32].try_into().unwrap()));
            if !merkle::verify_pair(hash,&[*v.folded_root.unwrap();2],FibreIndex::new(u as usize/4).unwrap(),[leaf;2],&[path;2])||values[u as usize%4]!=folded{return Err(Error::Query);}
            folded=second_fold(folding[1],u as usize,values);trace::value(10,2*i+1,folded);
        }
        let mut node=r0::domain::line_node::<E>(FibreIndex::new(if v.variant.folds()==1 {u as usize}else{u as usize/4*4}).unwrap());
        if v.variant.folds()==2 {for _ in 0..2 {let square=node.mul(node);node=square.add(square).sub(E::ONE);}}
        for j in 0..final_message.len(){let weight=r0::basis::natural(j,node);batch_weights[j]=batch_weights[j].add(rho_power.mul(weight));trace::value(12,i*final_message.len()+j,batch_weights[j]);trace::value(13,i*final_message.len()+j,weight);}
        rhs=rhs.add(rho_power.mul(folded));trace::value(11,i,rhs);rho_power=rho_power.mul(rho);
    }
    for r in 0..folding.len(){let b=if r==0 {v.round0}else{v.round1};let p:Vec<E>=(0..7).map(|j|value(b,j)).collect();let left=p[0].add(p[4]);let right=relation.mul(E::from_m31(M31(536870912)));trace::value(15,3*r,left);trace::value(15,3*r+1,right);if left!=right{return Err(Error::Relation);}relation=eval(&p,folding[r]);trace::value(15,3*r+2,relation);}
    let points=r0::opening::points_from_alphas(&alpha.map(E::from_qm31));let mut paired=[E::ZERO;7];
    for kind in 0..7 {
        let mut weights:Vec<E>=(0..1024).map(|j|match kind {
            0=>if r0::opening::inactive(row(v.variant,j)).unwrap(){E::ONE}else{E::ZERO},
            1..=3=>(0..10).fold(E::ONE,|a,b|a.mul(if (row(v.variant,j)>>b)&1==0 {E::ONE.sub(points[kind-1][b])}else{points[kind-1][b]})),
            4=>if j<56 {powers(E::from_qm31(alpha[8+j/28]),28)[j%28]}else{E::ZERO},
            _=>{let p=Point{x:E::from_qm31(z[kind-5].x),y:E::from_qm31(z[kind-5].y)};r0::basis::natural(j/2,p.x).mul(if j%2==0 {E::ONE}else{p.y})}
        }).collect();
        for (j,&x) in weights.iter().enumerate(){trace::value(6,kind*1024+j,x);}
        for &alpha in &folding {let p=powers(alpha,4);weights=weights.chunks_exact(4).map(|c|c[0].add(p[3].mul(c[1])).add(p[2].mul(c[2])).add(p[1].mul(c[3])).mul(E::from_m31(M31(536870912)))).collect();}
        for (j,&x) in weights.iter().enumerate(){trace::value(7,kind*final_message.len()+j,x);}
        paired[kind]=dot(&final_message,&weights);trace::value(8,kind,paired[kind]);
    }
    let pair=dot(&paired,&kp);trace::value(16,0,pair);trace::value(16,1,relation);if pair!=relation{return Err(Error::Relation);}
    let actual=dot(&final_message,&batch_weights);trace::value(17,0,actual);trace::value(17,1,rhs);if actual!=rhs{return Err(Error::Query);}Ok(())
}
