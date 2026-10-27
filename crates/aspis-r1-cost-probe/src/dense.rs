//! UNPROVED COST PROBE. Dense native self-consistency evaluator.
//! Uses E arithmetic, literal 1024-entry rows and original circle folding.
//! Adopted format (PREREG-PROOF-SIZE-2): reads the compact binary-multiproof
//! proof with its own expansion, canonical scan and BTreeMap multiproof
//! reconstruction (independent of `verifier::candidate`); layout constants
//! come from `crate::compact`.
use aspis_core::r0::CodeField;
use alloc::{collections::BTreeMap,vec,vec::Vec};
use aspis_core::{HashFn,field::{WideExact as E,QM31 as K,M31},r0::{self,domain::{FibreIndex,Point},merkle},r0_transcript as sample};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
use crate::{compact as c,r1_wire as wire,trace,transport::Variant,verifier::Error};
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
    let x=if nonzero {crate::host_sampler::gamma_sample(&block)}else{crate::host_sampler::ordinary_sample(&block)};trace::value(4,row as usize,x);x
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
/// The compact proof viewed in its logical (32-byte value) form.
struct Dense { variant:Variant, semantic:Vec<u8>, y1:Vec<u8>, inactive:E }
fn expand(src:&[u8],dst:&mut Vec<u8>) {for v in src.chunks_exact(16){dst.extend_from_slice(v);dst.extend_from_slice(&[0;16]);}}
fn wide_ok(b:&[u8])->bool {b.chunks_exact(32).all(|x|E::from_le_bytes(x).is_some())}
fn parse(proof:&[u8])->Result<Dense,Error> {
    if proof.len()!=c::PROOF_BYTES||&proof[..8]!=c::MAGIC||proof[8]!=Variant::S2.tag()||proof[9..16].iter().any(|&b|b!=0) {return Err(Error::Parse);}
    let mut semantic=Vec::with_capacity(c::LOGICAL_SEMANTIC);
    let src=&proof[c::OFF_SEMANTIC..c::OFF_Y1];semantic.extend_from_slice(&src[..32]);let mut at=32;
    for row in 0..c::SEMANTIC_ROWS {
        let size=wire::row_shape(row).ok_or(Error::Parse)?.1;semantic.extend_from_slice(&src[at..at+5]);at+=5;
        if row>=14 {expand(&src[at..at+size/2],&mut semantic);at+=size/2;} else {semantic.extend_from_slice(&src[at..at+size]);at+=size;}
    }
    if at!=src.len()||semantic.len()!=c::LOGICAL_SEMANTIC {return Err(Error::Parse);}
    let mut y1=Vec::with_capacity(c::LOGICAL_Y1);expand(&proof[c::OFF_Y1..c::OFF_INACTIVE],&mut y1);
    // Every value read below is canonical (the helpers unwrap).
    if !wide_ok(&y1)||!wide_ok(&proof[c::OFF_INACTIVE..c::OFF_FOLDED_ROOT])||!wide_ok(&proof[c::OFF_ROUND1..c::OFF_OPENINGS]) {return Err(Error::Parse);}
    for i in 0..22 {
        let q=&proof[c::OFF_OPENINGS+i*c::OPENING..][..c::OPENING];
        for s in 0..4 {
            if (0..26).any(|l|M31::from_le_bytes(q[s*120+l*4..s*120+l*4+4].try_into().unwrap()).is_none())||K::from_le_bytes(&q[s*120+104..s*120+120]).is_none()
                ||(0..2).any(|l|K::from_le_bytes(&q[480+s*32+l*16..480+s*32+l*16+16]).is_none()) {return Err(Error::Parse);}
        }
        if !wide_ok(&q[672..800]) {return Err(Error::Parse);}
    }
    let inactive=E::from_le_bytes(&proof[c::OFF_INACTIVE..c::OFF_ROUND0]).unwrap();
    Ok(Dense{variant:Variant::S2,semantic,y1,inactive})
}
/// Binary multiproof by explicit level maps: occupied nodes keyed by index,
/// siblings taken from `slot` in ascending order, the slot's unused tail zero.
fn multiproof(hash:HashFn,root:&[u8;32],leaves:BTreeMap<u32,[u8;32]>,slot:&[u8])->bool {
    let mut level=leaves;let mut at=0usize;
    let take=|at:&mut usize|->Option<[u8;32]> {let x=slot.get(*at..*at+32)?.try_into().ok()?;*at+=32;Some(x)};
    for _ in 0..18 {
        let keys:Vec<u32>=level.keys().copied().collect();let mut next=BTreeMap::new();let mut i=0;
        while i<keys.len() {
            let k=keys[i];
            let (l,r)=if k&1==0 {
                if i+1<keys.len()&&keys[i+1]==k+1 {i+=2;(level[&k],level[&(k+1)])} else {i+=1;let Some(s)=take(&mut at) else {return false};(level[&k],s)}
            } else {i+=1;let Some(s)=take(&mut at) else {return false};(s,level[&k])};
            next.insert(k>>1,hash(&[&[0x12],&l,&r]));
        }
        level=next;
    }
    level.len()==1&&level.get(&0)==Some(root)&&slot[at..].iter().all(|&b|b==0)
}
pub fn verify(public:Public<'_>,proof:&[u8],hash:HashFn)->Result<(),Error> {
    let v=parse(proof)?;let prefix=wire::Prefix::parse(&v.semantic).map_err(|_|Error::Parse)?;
    let round0=&proof[c::OFF_ROUND0..c::OFF_FOLDED_ROOT];let folded_root:[u8;32]=proof[c::OFF_FOLDED_ROOT..c::OFF_ROUND1].try_into().unwrap();
    let round1=&proof[c::OFF_ROUND1..c::OFF_FINAL];let final_bytes=&proof[c::OFF_FINAL..c::OFF_OPENINGS];
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
    let gamma=scalar(hash,&mut state,27,&v.y1,true);let kappa=scalar(hash,&mut state,28,&v.inactive.to_le_bytes(),false);
    let mut folding=vec![scalar(hash,&mut state,29,round0,false)];
    {let mut b=folded_root.to_vec();b.extend_from_slice(round1);folding.push(scalar(hash,&mut state,30,&b,false));}
    let query_row=31;let queries=queries(hash,&mut state,query_row,final_bytes)?;
    absorb(hash,&mut state,query_row+1,&[]);let block=hash(&[&state,&[1]]);state=hash(&[&state,&[2]]);
    let rho=E::from_qm31(sample::qm31_sample(&block));trace::value(4,(query_row+1) as usize,rho);let gp=powers(gamma,29);let kp=powers(kappa,7);
    let mut claims_batch=[E::ZERO;7];claims_batch[0]=v.inactive;
    for p in 0..3 {claims_batch[p+1]=dot(&gp,&claims[p]);}
    claims_batch[4]=dot(&gp,&extra);
    let endpoints:Vec<E>=(0..29).map(|l|value(prefix.payload(26).unwrap(),l)).collect();claims_batch[5]=dot(&gp,&endpoints);
    let endpoints:Vec<E>=(0..29).map(|l|value(&v.y1,l)).collect();claims_batch[6]=dot(&gp,&endpoints);
    for (j,&x) in claims_batch.iter().enumerate(){trace::value(14,j,x);}let mut relation=dot(&kp,&claims_batch);trace::value(14,7,relation);
    let final_message:Vec<E>=(0..v.variant.final_len()).map(|j|value(final_bytes,j)).collect();
    let mut batch_weights=vec![E::ZERO;final_message.len()];let mut rhs=E::ZERO;let mut rho_power=E::ONE;
    let roots=[*prefix.c1_root,prefix.payload(2).unwrap().try_into().unwrap()];
    // Batch multiproofs: queries 0..10 then 10..22; C1, C2, folded (u/4).
    let opening=|i:usize|&proof[c::OFF_OPENINGS+i*c::OPENING..][..c::OPENING];
    for (batch,(lo,hi)) in [(0,10),(10,22)].into_iter().enumerate() {
        for tree in 0..3 {
            let mut leaves=BTreeMap::new();
            for i in lo..hi {
                let q=opening(i);let u=queries[i];
                let (index,leaf)=match tree {
                    0=>(u,hash(&[&[0x10,merkle::C1_TAG],&q[..480],&q[608..640]])),
                    1=>(u,hash(&[&[0x10,merkle::C2_TAG],&q[480..608],&q[640..672]])),
                    _=>(u/4,hash(&[&[0x10,0x72],&q[672..800],&q[800..832]])),
                };
                if let Some(old)=leaves.insert(index,leaf) {if old!=leaf {return Err(Error::Merkle);}}
            }
            let slot=3*batch+tree;let start=c::OFF_NODES+32*c::SLOT_NODES[..slot].iter().sum::<usize>();
            let root=if tree==2 {&folded_root} else {&roots[tree]};
            if !multiproof(hash,root,leaves,&proof[start..start+32*c::SLOT_NODES[slot]]) {return Err(Error::Merkle);}
        }
    }
    for (i,&u) in queries.iter().enumerate() {
        let q=opening(i);
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
        {
            let b=&q[672..800];let values=core::array::from_fn(|s|value(b,s));
            if values[u as usize%4]!=folded{return Err(Error::Query);}
            folded=second_fold(folding[1],u as usize,values);trace::value(10,2*i+1,folded);
        }
        let mut node=r0::domain::line_node::<E>(FibreIndex::new(if v.variant.folds()==1 {u as usize}else{u as usize/4*4}).unwrap());
        if v.variant.folds()==2 {for _ in 0..2 {let square=node.mul(node);node=square.add(square).sub(E::ONE);}}
        for j in 0..final_message.len(){let weight=r0::basis::natural(j,node);batch_weights[j]=batch_weights[j].add(rho_power.mul(weight));trace::value(12,i*final_message.len()+j,batch_weights[j]);trace::value(13,i*final_message.len()+j,weight);}
        rhs=rhs.add(rho_power.mul(folded));trace::value(11,i,rhs);rho_power=rho_power.mul(rho);
    }
    for r in 0..folding.len(){let b=if r==0 {round0}else{round1};let p:Vec<E>=(0..7).map(|j|value(b,j)).collect();let left=p[0].add(p[4]);let right=relation.mul(E::from_m31(M31(536870912)));trace::value(15,3*r,left);trace::value(15,3*r+1,right);if left!=right{return Err(Error::Relation);}relation=eval(&p,folding[r]);trace::value(15,3*r+2,relation);}
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
