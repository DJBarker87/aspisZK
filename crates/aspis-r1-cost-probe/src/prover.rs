//! UNPROVED COST PROBE. Own native prover, including D14 content.
use alloc::{vec,vec::Vec};
use aspis_core::{HashFn,field::{WideExact as E,M31,QM31 as K,CM31},r0::{self,CodeField,domain::{Point,FibreIndex},merkle,wire::FibreOpening,Message}};
use aspis_statement::pool_v1::{pair_forest_semantic_terminal::r0::Public,pair_forest_trace::PoolV1PairForestMergedC1CompilationV1};
use crate::{transport::Variant,verifier::{Error,View},weights::{Weights,QUARTER,PERM},transcript::Transcript,host_commitment::{Commitment,CommitmentTime,EncodingDomain},host_semantic::{Column,Commitments},r1_wire::Error as SError};
pub struct Backend {pub hash:HashFn,pub variant:Variant,pub domain:EncodingDomain,pub messages:Vec<Message<E>>,pub c1:Option<Commitment>,pub c2:Option<Commitment>}
impl Commitments for Backend {
    fn c1(&mut self,columns:[Column<'_>;27])->Result<[u8;32],SError>{
        for (i,c) in columns.into_iter().enumerate(){self.messages[if i<26{i}else{28}]=match c {Column::Base(v)=>v.map(E::from_m31),Column::Extension(v)=>v.map(E::from_qm31)};}
        let c=Commitment::new(self.hash,&self.domain,CommitmentTime::C1,&self.messages,self.variant).map_err(|_|SError::Public)?;
        let root=c.root();self.c1=Some(c);Ok(root)
    }
    fn c2(&mut self,columns:[&[K;1024];2])->Result<[u8;32],SError>{
        for (i,c) in columns.into_iter().enumerate(){self.messages[26+i]=c.map(E::from_qm31);}
        let c=Commitment::new(self.hash,&self.domain,CommitmentTime::C2,&self.messages,self.variant).map_err(|_|SError::Public)?;
        let root=c.root();self.c2=Some(c);Ok(root)
    }
}
pub fn round(q:&[E],w:&[E])->[E;7] {
    assert_eq!(q.len(),w.len());let mut c=[E::ZERO;7];
    for d in 0..q.len()/4 {for s in 0..4 {for t in 0..4 {c[s+PERM[t]]=c[s+PERM[t]].add(q[4*d+s].mul(w[4*d+t]));}}}
    c.map(|x|x.mul_m31(QUARTER))
}
pub fn fold(q:&[E],alpha:E,dual:bool)->Vec<E> {
    q.chunks_exact(4).map(|h| {
        if dual {h[0].add(alpha.mul(h[3].add(alpha.mul(h[2].add(alpha.mul(h[1])))))).mul_m31(QUARTER)}
        else {h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))}
    }).collect()
}
pub fn encoded(values:impl IntoIterator<Item=E>)->Vec<u8> {values.into_iter().flat_map(E::to_le_bytes).collect()}

/// Deterministic fixture-only rejection sampling of K limbs. No distribution
/// property is inferred from these fixed test samples.
fn tail_samples(hash:HashFn,seed:&[u8;32])->[K;56] {
    let mut counter=0u64;
    let mut limb=||loop {
        let b=hash(&[b"UNPROVED:R1:P2:fixture-tail",seed,&counter.to_le_bytes()]);counter+=1;
        let x=u32::from_le_bytes(b[..4].try_into().unwrap())&0x7fffffff;
        if x<aspis_core::field::P {break M31(x);}
    };
    core::array::from_fn(|_|K{c0:CM31::new(limb(),limb()),c1:CM31::new(limb(),limb())})
}
pub fn prove(public:Public<'_>,compiled:&PoolV1PairForestMergedC1CompilationV1,variant:Variant,hash:HashFn,seed:&[u8;32])->Result<Vec<u8>,Error> {
    let masks=core::array::from_fn(|l|(0..1024).map(|r|M31(((l+16)*103+r*7+19)as u32)).collect());
    let mut dc=core::array::from_fn(|r|K{c0:CM31::new(M31(r as u32+3),M31(11)),c1:CM31::new(M31(17),M31(19))});
    dc[..56].copy_from_slice(&tail_samples(hash,seed));let d=variant.rows(&dc);
    let g=core::array::from_fn(|r|K::from_m31(M31(r as u32+5)));
    let mut backend=Backend{hash,variant,domain:EncodingDomain::new().map_err(|_|Error::Allocation)?,messages:vec![[E::ZERO;1024];29],c1:None,c2:None};
    let sem=crate::host_semantic::build(public,compiled,&masks,&d,&g,&mut backend,hash,variant).map_err(|_|Error::Semantic)?;
    let coefficients:Vec<Message<E>>=backend.messages.iter().map(|m|variant.coefficients(m)).collect();
    let z1=Point{x:E::from_qm31(sem.z[1].x),y:E::from_qm31(sem.z[1].y)};
    let y1=encoded(coefficients.iter().map(|m|r0::encoder::eval_message(m,z1)));
    let mut t=Transcript::new(hash,sem.transcript.state(),variant);
    let gamma=t.scalar(27,&y1,true);let gp=crate::weights::powers::<29>(gamma);
    let q:Vec<E>=(0..1024).map(|j|(0..29).fold(E::ZERO,|s,l|s.add(gp[l].mul(coefficients[l][j])))).collect();
    let w=Weights::new(variant,&sem.alpha,&sem.z)?;
    let inactive=(0..1024).fold(E::ZERO,|s,j|s.add(q[j].mul_qm31(w.raw(0,j))));
    let kappa=t.scalar(28,&inactive.to_le_bytes(),false);
    let weights=w.materialize(kappa)?;
    let c0=round(&q,&weights);let c0bytes=encoded(c0);
    let alpha0=t.scalar(29,&c0bytes,false);let q1=fold(&q,alpha0,false);let w1=fold(&weights,alpha0,true);
    let mut folded_tree=None;let mut folded_word=Vec::new();let mut root=[0;32];let mut c1bytes=Vec::new();
    let final_message=if variant.folds()==2 {
        folded_word=backend.domain.evaluate(&q1,0).map_err(|_|Error::Allocation)?;
        let mut leaves=Vec::with_capacity(1<<18);
        for u in 0..1<<18 {let values=if u<1<<16 {encoded(folded_word[4*u..4*u+4].iter().copied())}else{vec![0;128]};leaves.push(merkle::leaf(hash,0x72,&values));}
        let tree=merkle::Tree::new(hash,leaves).map_err(|_|Error::Allocation)?;root=tree.root();folded_tree=Some(tree);
        let c1=round(&q1,&w1);c1bytes=encoded(c1);
        let mut payload=root.to_vec();payload.extend_from_slice(&c1bytes);
        let alpha1=t.scalar(30,&payload,false);fold(&q1,alpha1,false)
    }else{q1};
    let fbytes=encoded(final_message.iter().copied());let row=if variant.folds()==1 {30}else{31};
    let queries=t.queries(row,&fbytes)?;let _rho=t.scalar(row+1,&[],false);
    let mut out=Vec::with_capacity(View::proof_bytes(variant));out.extend_from_slice(b"R1P2COST");out.extend_from_slice(&[variant.tag(),0,0,0,0,0,0,0]);
    assert_eq!(sem.bytes.len(),crate::verifier::SEMANTIC_BYTES);out.extend_from_slice(&sem.bytes);out.extend_from_slice(&y1);out.extend_from_slice(&inactive.to_le_bytes());out.extend_from_slice(&c0bytes);
    if variant.folds()==2 {out.extend_from_slice(&root);out.extend_from_slice(&c1bytes);}
    out.extend_from_slice(&fbytes);
    for u in queries {
        let u=FibreIndex::new(u as usize).unwrap();
        let mut opening=FibreOpening{values:[[E::ZERO;29];4],paths:[[[[0;32];7];6];2]};
        backend.c1.as_ref().unwrap().fill_opening(u,&mut opening);backend.c2.as_ref().unwrap().fill_opening(u,&mut opening);
        for s in 0..4 {for l in (0..26).chain(core::iter::once(28)){out.extend_from_slice(&opening.values[s][l].to_le_bytes()[..if l<26 {4}else{16}]);}}
        for s in 0..4 {for l in 26..28 {out.extend_from_slice(&opening.values[s][l].to_le_bytes()[..16]);}}
        for path in opening.paths {for level in path {for digest in level {out.extend_from_slice(&digest);}}}
        if variant.folds()==2 {
            out.extend_from_slice(&encoded(folded_word[4*(u.get()/4)..4*(u.get()/4)+4].iter().copied()));
            for level in folded_tree.as_ref().unwrap().path(FibreIndex::new(u.get()/4).unwrap()){for digest in level{out.extend_from_slice(&digest);}}
        }
    }
    assert_eq!(out.len(),View::proof_bytes(variant));Ok(out)
}
