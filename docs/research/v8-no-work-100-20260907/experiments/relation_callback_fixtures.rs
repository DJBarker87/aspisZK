//! Prover/test side only. Full vectors/trees never enter verify_relation.
use super::*;
use std::collections::BTreeSet;
use std::cell::RefCell;
thread_local! {static HASH_STATS: RefCell<[usize;4]> = const {RefCell::new([0;4])};}
fn metered_hash(parts:&[&[u8]])->[u8;32]{
    let n=parts.iter().map(|p|p.len()).sum::<usize>();
    HASH_STATS.with(|s|{let mut s=s.borrow_mut();s[0]+=1;s[1]+=n;s[2]+=(n+9).div_ceil(64);
        if parts.len()==1&&n==53&&parts[0][0]==0x11{s[3]+=1;}});
    hash(parts)
}
fn tpower(mut x:K,n:usize)->K{for _ in 0..n.trailing_zeros(){x=x.square().add(x.square()).sub(K::ONE);}x}
fn record(x:M31,n:usize)->Vec<u8>{
    let value=tpower(sc(x.0),n).c0.a.0;let mut r=vec![0u8;REC];
    for slot in 0..4{let bit=31*26*slot;for j in 0..31{r[(bit+j)/8]|=(((value>>j)&1)as u8)<<((bit+j)%8);}}
    r
}
type Tree=Vec<Vec<[u8;26]>>;
fn trees(n:usize)->(Tree,Tree){
    let ids:Vec<u32>=(0..1<<18).collect();let points=corelib::circle_fri::selected_circle_fiber_points_shared(20,&ids).unwrap();
    let leaves:Vec<[u8;26]>=points.iter().map(|p|private_leaf_hash_v7(hash,V7_C1_TREE_TAG,&record(p.x,n)[..403],&[0;32])).collect();
    let mut a=vec![leaves];for _ in 0..18{let next=a.last().unwrap().chunks_exact(2).map(|v|node_hash_v7(hash,&v[0],&v[1])).collect();a.push(next);}
    let mut b=vec![vec![private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&[0;186],&[0;32])]];for _ in 0..18{let v=b.last().unwrap()[0];b.push(vec![node_hash_v7(hash,&v,&v)]);}(a,b)
}
fn frontier(tree:&Tree,queries:&[u32])->Vec<u8>{let mut out=vec![];let mut nodes:BTreeSet<u32>=queries.iter().copied().collect();
    for row in tree.iter().take(18){for &j in &nodes{if !nodes.contains(&(j^1)){out.extend_from_slice(&row[if row.len()==1{0}else{(j^1)as usize}]);}}nodes=nodes.into_iter().map(|j|j>>1).collect();}out}
fn body(v:&[K],a:&Tree,b:&Tree,records:&[u8],front:(&[u8],&[u8]))->Vec<u8>{let mut out=bytes(v);out.extend_from_slice(&a[18][0]);out.extend_from_slice(&b[18][0]);out.extend_from_slice(&[0;24]);out.extend_from_slice(records);out.extend_from_slice(front.0);out.extend_from_slice(front.1);out}
fn next_cheb(t:&[K],prev:&[K])->Vec<K>{let mut n=vec![K::ZERO;t.len()+1];for(j,v)in t.iter().enumerate(){n[j+1]=v.add(*v);}for(j,v)in prev.iter().enumerate(){n[j]=n[j].sub(*v);}n}
fn monomial_product(a:&[M31],b:&[M31])->Vec<M31>{let mut r=vec![M31::ZERO;a.len()+b.len()-1];for(i,x)in a.iter().enumerate(){for(j,y)in b.iter().enumerate(){r[i+j]=r[i+j].add(x.mul(*y));}}r}
fn tensor_basis()->Vec<Vec<M31>>{
    let mut chebs=vec![vec![M31::ONE],vec![M31::ZERO,M31::ONE]];
    for j in 2..512{let t=&chebs[j-1];let prev=&chebs[j-2];let mut r=vec![M31::ZERO;j+1];for(k,v)in t.iter().enumerate(){r[k+1]=v.double();}for(k,v)in prev.iter().enumerate(){r[k]=r[k].sub(*v);}chebs.push(r);}
    let mut basis=vec![vec![M31::ONE]];for j in 1usize..512{let high=1<<(usize::BITS-1-j.leading_zeros());basis.push(monomial_product(&basis[j-high],&chebs[high]));}basis
}
fn natural(mut a:Vec<K>,mut b:Vec<K>)->Vec<K>{a.resize(512,K::ZERO);b.resize(512,K::ZERO);let basis=tensor_basis();let mut q=vec![K::ZERO;1024];
    for j in (0..512).rev(){let inv=basis[j][j].inv();q[2*j]=a[j].mul_m31(inv);q[2*j+1]=b[j].mul_m31(inv);
        for k in 0..=j{a[k]=a[k].sub(q[2*j].mul_m31(basis[j][k]));b[k]=b[k].sub(q[2*j+1].mul_m31(basis[j][k]));}}
    assert!(a.iter().chain(&b).all(|x|*x==K::ZERO));q
}
fn quotient(n:usize,p:&Prefix)->Vec<K>{
    let i=K::from_cm31(CM31::new(M31::ZERO,M31::ONE));let[a,b,c]=p.abc;
    let lo=b.add(i.mul(c)).half();let hi=b.sub(i.mul(c)).half();
    let mut num=vec![K::ZERO;2*n+1];num[0]=K::ONE.half();num[2*n]=K::ONE.half();num[n]=p.iv[0].neg();
    let(il,ih)=if p.use_x{(p.iv[1].half(),p.iv[1].half())}else{(i.mul(p.iv[1]).half(),i.mul(p.iv[1]).half().neg())};
    num[n-1]=num[n-1].sub(il);num[n+1]=num[n+1].sub(ih);
    let mut rem=num.clone();let mut q=vec![K::ZERO;2*n-1];let inv=hi.try_inv().unwrap();
    for j in (2..rem.len()).rev(){let v=rem[j].mul(inv);q[j-2]=v;rem[j]=K::ZERO;rem[j-1]=rem[j-1].sub(a.mul(v));rem[j-2]=rem[j-2].sub(lo.mul(v));}
    assert!(rem.iter().all(|v|*v==K::ZERO));
    let mut aa=vec![K::ZERO;n];let mut bb=vec![K::ZERO;n];aa[0]=q[n-1];let mut tm=vec![K::ONE];let mut t=vec![K::ZERO,K::ONE];let mut um=vec![];let mut u=vec![K::ONE];
    for j in 1..n{let plus=q[n-1+j];let minus=q[n-1-j];for(k,v)in t.iter().enumerate(){aa[k]=aa[k].add(v.mul(plus.add(minus)));}for(k,v)in u.iter().enumerate(){bb[k]=bb[k].add(v.mul(i.mul(plus.sub(minus))));}
        let tn=next_cheb(&t,&tm);tm=t;t=tn;let un=next_cheb(&u,&um);um=u;u=un;}
    let q=natural(aa,bb);assert_eq!(q[1023],K::ZERO);
    assert_eq!(b.mul(q[1022]).sub(c.mul(q[1021])),if n==512{sc(512)}else{K::ZERO});q
}
fn save_round(v:&mut[K],r:usize,p:[K;7]){v[417+r*6..423+r*6].copy_from_slice(&[p[0],p[1],p[2],p[3],p[5],p[6]]);}
fn ordinary_weights()->Vec<K>{(0..1024).map(|i|sc((i%7+1)as u32)).collect()}
fn proof(n:usize,a:&Tree,b:&Tree,alter:bool)->(Vec<u8>,K){
    let mut v=vec![K::ZERO;697];let ordinary=ordinary_weights();let stub=body(&v,a,b,&vec![0;Q*REC],(&[],&[]));let w=parse(&stub).unwrap();
    let mut t=before_ood(&w,&[7;32],hash).unwrap();let s=t.challenge_secure_circle_point().unwrap();v[359]=tpower(s.x,n);
    let mut rec=vec![0];rec.extend(bytes(&v[359..388]));t.absorb(V8_COMPONENT_OOD_VECTOR,&rec);
    let z=loop{let p=t.challenge_secure_circle_point().unwrap();if p!=s{break p;}};v[388]=tpower(z.x,n);
    let stub=body(&v,a,b,&vec![0;Q*REC],(&[],&[]));let w=parse(&stub).unwrap();let mut p=freeze(before_ood(&w,&[7;32],hash).unwrap(),&w,&ordinary,K::ZERO).unwrap();
    assert_eq!(p.points,[s,z]);let q=quotient(n,&p);
    let ordinary_claim=dot(&ordinary,&q);
    // Q/chord/gamma are fixed before the claim binding and tau. Rebuild only
    // the transcript boundary with the now-computed honest ordinary claim.
    p=freeze(before_ood(&w,&[7;32],hash).unwrap(),&w,&ordinary,ordinary_claim).unwrap();
    let mut image=vec![K::ZERO;1024];image[1023]=p.tau;image[1022]=p.tau.square().mul(p.abc[1]);image[1021]=p.tau.square().mul(p.abc[2]).neg();
    let mut weights=WeightAccumulator::empty(10);weights.add_dense(image).unwrap();weights.add_dense(ordinary).unwrap();let mut claim=ordinary_claim;
    save_round(&mut v,0,polynomial_for_extension(&q,&weights));let first=compact(&v[417..423],claim);absorb_round(&mut p.t,0,&first);
    p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&[0;9]);let alpha=sample(&mut p.t,false).unwrap();claim=evaluate(&first,alpha);weights.fold_deferred_relation_arity4(alpha);
    let truth=primal(&q,alpha);let mut finals=truth.clone();if alter{finals[0]=finals[0].add(K::ONE);}v[441..697].copy_from_slice(&finals);
    let(queries,rho)=query_schedule(&mut p,&finals,&[0;24]).unwrap();let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&queries).unwrap();
    let records:Vec<u8>=pts.iter().flat_map(|p|record(p.x,n)).collect();let fa=frontier(a,&queries);let fb=frontier(b,&queries);
    let tmp=body(&v,a,b,&records,(&fa,&fb));let wire=parse(&tmp).unwrap();let(values,xs)=opened_values(&wire,&p,&queries,alpha,hash).unwrap();
    for j in 0..Q{assert_eq!(values[j],corelib::v6_onefold::evaluate_final256_coefficients(&truth,xs[j]).unwrap());}
    let inc=inject(&mut weights,&mut claim,&values,&xs,rho).unwrap();p.t.absorb(label::PROFILE,&bytes(&[inc]));
    for r in 1..4{save_round(&mut v,r,polynomial_for_extension(&finals,&weights));let poly=compact(&v[417+r*6..423+r*6],claim);absorb_round(&mut p.t,r,&poly);let alpha=sample(&mut p.t,false).unwrap();claim=evaluate(&poly,alpha);weights.fold_deferred_relation_arity4(alpha);finals=primal(&finals,alpha);}
    (body(&v,a,b,&records,(&fa,&fb)),ordinary_claim)
}
fn invalid_hash(_: &[&[u8]])->[u8;32]{[255;32]}
fn zero_hash(_: &[&[u8]])->[u8;32]{[0;32]}
pub fn run(){
    for n in [2,512]{let(a,b)=trees(n);for alter in [false,true]{let(proof,ordinary_claim)=proof(n,&a,&b,alter);assert!(proof.len()<=40282);
        HASH_STATS.with(|s|*s.borrow_mut()=[0;4]);
        let result=verify_relation(&proof,[7;32],ordinary_weights(),ordinary_claim,metered_hash);
        if n==2&&!alter{assert_eq!(result,Ok(()));}else{assert_eq!(result,Err(Error::Terminal));}
        println!("n={n}, altered_final={alter}, body={}, relation_result={result:?}",proof.len());
        HASH_STATS.with(|s|println!("verifier-only [hash calls, input bytes, SHA256 padded blocks, internal Merkle hashes] = {:?}",s.borrow()));
        if n==2&&!alter{
            for cut in [0,1,HEAD-1,proof.len()-1]{assert!(verify_relation(&proof[..cut],[7;32],ordinary_weights(),ordinary_claim,hash).is_err());}
            let mut bad=proof.clone();bad[0..4].copy_from_slice(&corelib::field::P.to_le_bytes());assert_eq!(verify_relation(&bad,[7;32],ordinary_weights(),ordinary_claim,hash),Err(Error::Canonical));
            let mut bad=proof.clone();bad[HEAD..HEAD+4].fill(255);assert_eq!(verify_relation(&bad,[7;32],ordinary_weights(),ordinary_claim,hash),Err(Error::Canonical));
            let mut bad=proof.clone();let last=bad.len()-1;bad[last]^=1;assert_eq!(verify_relation(&bad,[7;32],ordinary_weights(),ordinary_claim,hash),Err(Error::Authentication));
            assert_eq!(verify_relation(&proof,[7;32],ordinary_weights(),ordinary_claim,invalid_hash),Err(Error::Sampler));
            assert_eq!(verify_relation(&proof,[7;32],ordinary_weights(),ordinary_claim,zero_hash),Err(Error::Sampler));
            assert!(verify_relation(&proof,[8;32],ordinary_weights(),ordinary_claim,hash).is_err());
        }
    }}
    println!("PASS actual SHA-256/Merkle/canonical compact relation suffix; no payment semantic validation or CU claim");
}
