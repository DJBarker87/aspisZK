//! UNPROVED COST PROBE. Own native prover, including D14 content.
use alloc::{vec,vec::Vec};
use aspis_core::{HashFn,field::{WideExact as E,M31,QM31 as K,CM31},r0::{self,CodeField,domain::{Point,FibreIndex},merkle,wire::FibreOpening,Message},state_only_hiding::StateOnlyHidingContext};
use aspis_statement::pool_v1::{pair_forest_semantic_terminal::r0::Public,pair_forest_trace::PoolV1PairForestMergedC1CompilationV1};
use aspis_statement::pool_v1::pool_v1_pair_forest_copy_active_row_masks_v1;
use aspis_prover::{state_only_entropy::{StateOnlyAttemptSecrets,ReservedStateOnlyAttemptSecrets,DurableStateOnlyMaskNonceStore},state_only_hiding::{apply_pool_v1_pair_forest_mask_material_v1,InMemoryStateOnlyMaskNonceStore,StateOnlyMaskNonceStore}};
use crate::{transport::Variant,verifier::{Error,View},weights::{Weights,QUARTER,PERM},transcript::Transcript,host_commitment::{Commitment,CommitmentTime,EncodingDomain,PrivateSalts},host_semantic::{BuiltSemantics,Column,Commitments},r1_wire::Error as SError};
pub struct Backend {pub hash:HashFn,pub variant:Variant,pub domain:EncodingDomain,pub messages:Vec<Message<E>>,pub c1:Option<Commitment>,pub c2:Option<Commitment>,c1_salts:Option<crate::host_commitment::PrivateSalts>,c2_salts:Option<crate::host_commitment::PrivateSalts>}
impl Commitments for Backend {
    fn c1(&mut self,columns:[Column<'_>;27])->Result<[u8;32],SError>{
        for (i,c) in columns.into_iter().enumerate(){self.messages[if i<26{i}else{28}]=match c {Column::Base(v)=>v.map(E::from_m31),Column::Extension(v)=>v.map(E::from_qm31)};}
        let c=if let Some(salts)=self.c1_salts.take(){Commitment::new_salted(self.hash,&self.domain,CommitmentTime::C1,&self.messages,self.variant,salts)}else{Commitment::new(self.hash,&self.domain,CommitmentTime::C1,&self.messages,self.variant)}.map_err(|_|SError::Public)?;
        let root=c.root();self.c1=Some(c);Ok(root)
    }
    fn c2(&mut self,columns:[&[K;1024];2])->Result<[u8;32],SError>{
        for (i,c) in columns.into_iter().enumerate(){self.messages[26+i]=c.map(E::from_qm31);}
        let c=if let Some(salts)=self.c2_salts.take(){Commitment::new_salted(self.hash,&self.domain,CommitmentTime::C2,&self.messages,self.variant,salts)}else{Commitment::new(self.hash,&self.domain,CommitmentTime::C2,&self.messages,self.variant)}.map_err(|_|SError::Public)?;
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
#[cfg(not(feature="private-leaf-salts"))]
pub fn prove(public:Public<'_>,compiled:&PoolV1PairForestMergedC1CompilationV1,variant:Variant,hash:HashFn,seed:&[u8;32])->Result<Vec<u8>,Error> {
    let masks=core::array::from_fn(|l|(0..1024).map(|r|M31(((l+16)*103+r*7+19)as u32)).collect());
    let mut dc=core::array::from_fn(|r|K{c0:CM31::new(M31(r as u32+3),M31(11)),c1:CM31::new(M31(17),M31(19))});
    dc[..56].copy_from_slice(&tail_samples(hash,seed));let d=variant.rows(&dc);
    let g=core::array::from_fn(|r|K::from_m31(M31(r as u32+5)));
    let mut backend=Backend{hash,variant,domain:EncodingDomain::new().map_err(|_|Error::Allocation)?,messages:vec![[E::ZERO;1024];29],c1:None,c2:None,c1_salts:None,c2_salts:None};
    let sem=crate::host_semantic::build(public,compiled,&masks,&d,&g,&mut backend,hash,variant).map_err(|_|Error::Semantic)?;
    prove_from_semantics(public,variant,hash,backend,sem,None)
}

/// Feature-enabled convenience API is deliberately fixture-only: it always
/// emits fully masked P3 proofs and cannot fall back to the unsalted P2 path.
#[cfg(feature="private-leaf-salts")]
pub fn prove(public:Public<'_>,compiled:&PoolV1PairForestMergedC1CompilationV1,variant:Variant,hash:HashFn,seed:&[u8;32])->Result<Vec<u8>,Error> {
    prove_masked_fixture(public,compiled,variant,hash,seed).map(|(proof,_)|proof)
}

/// Checks describing the fixture mask constraints exercised before proving.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaskedFixtureAudit {
    pub c1_columns_inactive_balanced: usize,
    pub mask_only_columns_inactive_balanced: usize,
    pub d_inactive_balanced: bool,
    pub g_inactive_balanced: bool,
    pub h1_padding_inactive_balanced: bool,
    pub h1_total_balanced: bool,
}

fn fixture_secret(hash:HashFn,domain:&[u8],seed:&[u8;32],public:&[u8],variant:Variant)->Result<[u8;32],Error> {
    let mut value=hash(&[domain,seed,public,&[variant.tag()]]);
    if value==[0;32] { return Err(Error::Semantic); }
    Ok(value)
}

fn inactive_sum_m31(values:&[M31],masks:&[u16;64])->M31 {
    values.iter().copied().enumerate().filter(|(row,_)| masks[row>>4]&(1<<(row&15))==0).fold(M31::ZERO,|sum,(_,value)|sum.add(value))
}

fn inactive_sum_k(values:&[K],masks:&[u16;64])->K {
    values.iter().copied().enumerate().filter(|(row,_)| masks[row>>4]&(1<<(row&15))==0).fold(K::ZERO,|sum,(_,value)|sum.add(value))
}

/// Deterministic, insecure masked fixture path. Its derivations exist only for
/// reproducible local cost experiments and are not production entropy.
pub fn prove_masked_fixture(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    fixture_seed:&[u8;32],
)->Result<(Vec<u8>,MaskedFixtureAudit),Error> {
    let public_bytes=public.public_bytes().map_err(|_|Error::Semantic)?;
    let context=StateOnlyHidingContext::pool_v1_pair_forest_v1(hash(&[&public_bytes]),fixture_secret(hash,b"UNPROVED:R1:fixture-mask-nonce",fixture_seed,&public_bytes,variant)?);
    #[cfg(not(feature="private-leaf-salts"))]
    let binding=hash(&[b"UNPROVED:R1:full-mask-fixture",&public_bytes,&[variant.tag()],&context.encode()]);
    #[cfg(feature="private-leaf-salts")]
    let binding=hash(&[b"UNPROVED:R1:P3:PRIVATE-ATTEMPT",&public_bytes,&[variant.tag()],&context.encode()]);
    let attempt=StateOnlyAttemptSecrets::deterministic_spend_fixture(
        context.mask_nonce,
        fixture_secret(hash,b"UNPROVED:R1:fixture-field-entropy",fixture_seed,&public_bytes,variant)?,
        fixture_secret(hash,b"UNPROVED:R1:fixture-leaf-seed",fixture_seed,&public_bytes,variant)?,
    );
    let mut nonce_store=InMemoryStateOnlyMaskNonceStore::default();
    prove_masked_with_attempt(public,compiled,variant,hash,context,binding,attempt,&mut nonce_store)
}

/// Secure-source P3 host API. Callers must supply OS-generated attempt
/// secrets and a durable nonce ledger; successful reservations happen before
/// mask derivation and leaf-salt derivation. This is still an UNPROVED
/// protocol: fresh entropy alone does not establish zero knowledge.
#[cfg(feature="private-leaf-salts")]
pub fn prove_masked_attempt(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    attempt:StateOnlyAttemptSecrets,
    nonce_store:&mut DurableStateOnlyMaskNonceStore,
)->Result<(Vec<u8>,MaskedFixtureAudit),Error> {
    let public_bytes=public.public_bytes().map_err(|_|Error::Semantic)?;
    let context=StateOnlyHidingContext::pool_v1_pair_forest_v1(hash(&[&public_bytes]),attempt.mask_nonce());
    let binding=hash(&[b"UNPROVED:R1:P3:PRIVATE-ATTEMPT",&public_bytes,&[variant.tag()],&context.encode()]);
    prove_masked_with_attempt(public,compiled,variant,hash,context,binding,attempt,nonce_store)
}

fn prove_masked_with_attempt(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    context:StateOnlyHidingContext,
    binding:[u8;32],
    attempt:StateOnlyAttemptSecrets,
    nonce_store:&mut impl StateOnlyMaskNonceStore,
)->Result<(Vec<u8>,MaskedFixtureAudit),Error> {
    let (reserved,material)=attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,binding,context,nonce_store).map_err(|_|Error::Semantic)?;
    let mut noised_c1=compiled.semantic_c1.clone();
    let applied=apply_pool_v1_pair_forest_mask_material_v1(&mut noised_c1,material).map_err(|_|Error::Semantic)?;
    let masks=pool_v1_pair_forest_copy_active_row_masks_v1().map_err(|_|Error::Semantic)?;
    let d: [K;1024]=reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,context).map_err(|_|Error::Semantic)?.try_into().map_err(|_|Error::Semantic)?;
    if applied.g.len()!=1024 || applied.h1_padding.len()!=1024 { return Err(Error::Semantic); }
    let g: [K;1024]=core::array::from_fn(|i|applied.g[i]);
    let h1_padding: [K;1024]=core::array::from_fn(|i|applied.h1_padding[i]);
    let c1_columns_inactive_balanced=noised_c1.c1.iter().filter(|column|inactive_sum_m31(column,&masks)==M31::ZERO).count();
    let mask_only_columns_inactive_balanced=applied.mask_only_c1.iter().filter(|column|inactive_sum_m31(column,&masks)==M31::ZERO).count();
    let audit=MaskedFixtureAudit{
        c1_columns_inactive_balanced,
        mask_only_columns_inactive_balanced,
        d_inactive_balanced:inactive_sum_k(&d,&masks)==K::ZERO,
        g_inactive_balanced:inactive_sum_k(&g,&masks)==K::ZERO,
        h1_padding_inactive_balanced:inactive_sum_k(&h1_padding,&masks)==K::ZERO,
        h1_total_balanced:true,
    };
    if audit.c1_columns_inactive_balanced!=16
        || audit.mask_only_columns_inactive_balanced!=10
        || !audit.d_inactive_balanced
        || !audit.g_inactive_balanced
        || !audit.h1_padding_inactive_balanced
    { return Err(Error::Semantic); }
    #[cfg(feature="private-leaf-salts")]
    let (c1_salts,c2_salts)=(Some(derive_private_salts(&reserved,context,hash,merkle::C1_TAG)?),Some(derive_private_salts(&reserved,context,hash,merkle::C2_TAG)?));
    #[cfg(not(feature="private-leaf-salts"))]
    let (c1_salts,c2_salts)=(None,None);
    let mut backend=Backend{hash,variant,domain:EncodingDomain::new().map_err(|_|Error::Allocation)?,messages:vec![[E::ZERO;1024];29],c1:None,c2:None,c1_salts,c2_salts};
    let sem=crate::host_semantic::build_with_material(public,compiled,&noised_c1,&applied.mask_only_c1,&d,&g,&h1_padding,&mut backend,hash,variant).map_err(|_|Error::Semantic)?;
    let h1_total_balanced=aspis_statement::state_only_copy_helper_sum(&sem.columns[26])==Some(K::ZERO);
    if !h1_total_balanced { return Err(Error::Semantic); }
    let audit=MaskedFixtureAudit{h1_total_balanced,..audit};
    #[cfg(feature="private-leaf-salts")]
    let proof=prove_from_semantics(public,variant,hash,backend,sem,Some((&reserved,context)))?;
    #[cfg(not(feature="private-leaf-salts"))]
    let proof=prove_from_semantics(public,variant,hash,backend,sem,None)?;
    Ok((proof,audit))
}

#[cfg(feature="private-leaf-salts")]
fn derive_private_salts(reserved:&ReservedStateOnlyAttemptSecrets,context:StateOnlyHidingContext,hash:HashFn,tag:u8)->Result<PrivateSalts,Error> {
    let mut salts=Vec::new();salts.try_reserve_exact(aspis_core::r0::FIBRE_COUNT).map_err(|_|Error::Allocation)?;
    for index in 0..aspis_core::r0::FIBRE_COUNT {
        salts.push(reserved.derive_pool_v1_leaf_salt(hash,context,tag,index as u32).map_err(|_|Error::Semantic)?);
    }
    Ok(PrivateSalts::new(salts))
}

fn prove_from_semantics(public:Public<'_>,variant:Variant,hash:HashFn,backend:Backend,sem:BuiltSemantics,salts:Option<(&ReservedStateOnlyAttemptSecrets,StateOnlyHidingContext)>)->Result<Vec<u8>,Error> {
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
    let mut folded_tree=None;let mut folded_word=Vec::new();
    #[cfg(feature="private-leaf-salts")]
    let mut folded_salts=None;
    let mut root=[0;32];let mut c1bytes=Vec::new();
    let final_message=if variant.folds()==2 {
        folded_word=backend.domain.evaluate(&q1,0).map_err(|_|Error::Allocation)?;
        let mut leaves=Vec::with_capacity(1<<18);
        #[cfg(feature="private-leaf-salts")]
        let (reserved,context)=salts.ok_or(Error::Semantic)?;
        #[cfg(feature="private-leaf-salts")]
        let folded_salts_value=derive_private_salts(reserved,context,hash,0x72)?;
        for u in 0..1<<18 {let values=if u<1<<16 {encoded(folded_word[4*u..4*u+4].iter().copied())}else{vec![0;128]};
            #[cfg(feature="private-leaf-salts")]
            let leaf=aspis_core::state_only_private_merkle::private_leaf_hash(hash,0x72,&values,folded_salts_value.get(u));
            #[cfg(not(feature="private-leaf-salts"))]
            let leaf=merkle::leaf(hash,0x72,&values);
            leaves.push(leaf);
        }
        #[cfg(feature="private-leaf-salts")]
        {folded_salts=Some(folded_salts_value);}
        let tree=merkle::Tree::new(hash,leaves).map_err(|_|Error::Allocation)?;root=tree.root();folded_tree=Some(tree);
        let c1=round(&q1,&w1);c1bytes=encoded(c1);
        let mut payload=root.to_vec();payload.extend_from_slice(&c1bytes);
        let alpha1=t.scalar(30,&payload,false);fold(&q1,alpha1,false)
    }else{q1};
    let fbytes=encoded(final_message.iter().copied());let row=if variant.folds()==1 {30}else{31};
    let queries=t.queries(row,&fbytes)?;let _rho=t.scalar_k(row+1,&[]);
    let mut out=Vec::with_capacity(View::proof_bytes(variant));
    #[cfg(not(feature="private-leaf-salts"))]
    out.extend_from_slice(b"R1P2COST");
    #[cfg(feature="private-leaf-salts")]
    out.extend_from_slice(b"R1P3COST");
    out.extend_from_slice(&[variant.tag(),0,0,0,0,0,0,0]);
    assert_eq!(sem.bytes.len(),crate::verifier::SEMANTIC_BYTES);out.extend_from_slice(&sem.bytes);out.extend_from_slice(&y1);out.extend_from_slice(&inactive.to_le_bytes());out.extend_from_slice(&c0bytes);
    if variant.folds()==2 {out.extend_from_slice(&root);out.extend_from_slice(&c1bytes);}
    out.extend_from_slice(&fbytes);
    for u in queries {
        let u=FibreIndex::new(u as usize).unwrap();
        let mut opening=FibreOpening{values:[[E::ZERO;29];4],paths:[[[[0;32];7];6];2]};
        backend.c1.as_ref().unwrap().fill_opening(u,&mut opening);backend.c2.as_ref().unwrap().fill_opening(u,&mut opening);
        for s in 0..4 {for l in (0..26).chain(core::iter::once(28)){out.extend_from_slice(&opening.values[s][l].to_le_bytes()[..if l<26 {4}else{16}]);}}
        for s in 0..4 {for l in 26..28 {out.extend_from_slice(&opening.values[s][l].to_le_bytes()[..16]);}}
        #[cfg(feature="private-leaf-salts")]
        {
            out.extend_from_slice(backend.c1.as_ref().unwrap().opening_salt(u).unwrap());
            out.extend_from_slice(backend.c2.as_ref().unwrap().opening_salt(u).unwrap());
        }
        for path in opening.paths {for level in path {for digest in level {out.extend_from_slice(&digest);}}}
        if variant.folds()==2 {
            out.extend_from_slice(&encoded(folded_word[4*(u.get()/4)..4*(u.get()/4)+4].iter().copied()));
            #[cfg(feature="private-leaf-salts")]
            out.extend_from_slice(folded_salts.as_ref().unwrap().get(u.get()/4));
            for level in folded_tree.as_ref().unwrap().path(FibreIndex::new(u.get()/4).unwrap()){for digest in level{out.extend_from_slice(&digest);}}
        }
    }
    assert_eq!(out.len(),View::proof_bytes(variant));Ok(out)
}
