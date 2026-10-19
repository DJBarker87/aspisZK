//! UNPROVED COST PROBE. Own native prover, including D14 content.
use alloc::{vec,vec::Vec};
use aspis_core::{digest::LegacyHashFn,HashFn,field::{WideExact as E,M31,QM31 as K,CM31},r0::{self,CodeField,domain::{Point,FibreIndex},merkle,wire::FibreOpening,Message},state_only_hiding::StateOnlyHidingContext};
use aspis_statement::pool_v1::{pair_forest_semantic_terminal::r0::Public,pair_forest_trace::PoolV1PairForestMergedC1CompilationV1};
use aspis_statement::pool_v1::pool_v1_pair_forest_copy_active_row_masks_v1;
use aspis_prover::{state_only_entropy::{StateOnlyAttemptSecrets,ReservedStateOnlyAttemptSecrets,DurableStateOnlyMaskNonceStore},state_only_hiding::{apply_pool_v1_pair_forest_mask_material_v1,InMemoryStateOnlyMaskNonceStore,StateOnlyMaskBuildError,StateOnlyMaskNonceStore}};
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
    let sem=crate::host_semantic::build(public,compiled,&masks,&d,&g,&mut backend,LegacyHashFn(hash),variant).map_err(|_|Error::Semantic)?;
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
    let (reserved,material)=attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,binding,context,nonce_store).map_err(mask_error)?;
    #[cfg(all(test,feature="r1p-check"))]
    if test_hooks::forced_exhaustion(reserved.mask_nonce()) { return Err(mask_error(StateOnlyMaskBuildError::MaskSampleExhausted)); }
    let mut noised_c1=compiled.semantic_c1.clone();
    let applied=apply_pool_v1_pair_forest_mask_material_v1(&mut noised_c1,material).map_err(|_|Error::Semantic)?;
    let masks=pool_v1_pair_forest_copy_active_row_masks_v1().map_err(|_|Error::Semantic)?;
    let d: [K;1024]=reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,context).map_err(mask_error)?.try_into().map_err(|_|Error::Semantic)?;
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
    #[cfg(all(test,feature="r1p-check"))]
    test_hooks::observe_secrets(hash,reserved.mask_nonce(),&g,c1_salts.as_ref().unwrap().get(0));
    #[cfg(not(feature="private-leaf-salts"))]
    let (c1_salts,c2_salts)=(None,None);
    let mut backend=Backend{hash,variant,domain:EncodingDomain::new().map_err(|_|Error::Allocation)?,messages:vec![[E::ZERO;1024];29],c1:None,c2:None,c1_salts,c2_salts};
    let sem=crate::host_semantic::build_with_material(public,compiled,&noised_c1,&applied.mask_only_c1,&d,&g,&h1_padding,&mut backend,LegacyHashFn(hash),variant).map_err(semantic_error)?;
    let h1_total_balanced=aspis_statement::state_only_copy_helper_sum(&sem.columns[26])==Some(K::ZERO);
    if !h1_total_balanced { return Err(Error::Semantic); }
    let audit=MaskedFixtureAudit{h1_total_balanced,..audit};
    #[cfg(feature="private-leaf-salts")]
    let proof=prove_from_semantics(public,variant,hash,backend,sem,Some((&reserved,context)))?;
    #[cfg(not(feature="private-leaf-salts"))]
    let proof=prove_from_semantics(public,variant,hash,backend,sem,None)?;
    Ok((proof,audit))
}

/// LOG D73.4.2: Lean `realGameP` rejects an attempt whose mask decode is
/// exhausted (`exh`, R1Z/GamesR1P.lean:164, 184) and moves to the next one.
/// With the retry loop, `MaskSampleExhausted` from either expander is
/// therefore a rejected attempt; every other mask error still aborts. Without
/// the loop (`r1p-check` off) behaviour is unchanged.
fn mask_error(e:StateOnlyMaskBuildError)->Error {
    #[cfg(feature="r1p-check")]
    if e==StateOnlyMaskBuildError::MaskSampleExhausted { return Error::Rejected; }
    let _=e;
    Error::Semantic
}

/// LOG D73.4.1: a LogUp pole (Lean `¬ VR1`, R1Z/MaskImageVR1.lean:29) is a
/// rejected attempt. The pole carries no detail; it becomes the same
/// `Error::Rejected` as a failed P_R1 check.
fn semantic_error(e:SError)->Error {
    #[cfg(feature="r1p-check")]
    if e==SError::ActivePole { return Error::Rejected; }
    let _=e;
    Error::Semantic
}

#[cfg(feature="private-leaf-salts")]
fn derive_private_salts(reserved:&ReservedStateOnlyAttemptSecrets,context:StateOnlyHidingContext,hash:HashFn,tag:u8)->Result<PrivateSalts,Error> {
    let mut salts=Vec::new();salts.try_reserve_exact(aspis_core::r0::FIBRE_COUNT).map_err(|_|Error::Allocation)?;
    for index in 0..aspis_core::r0::FIBRE_COUNT {
        salts.push(reserved.derive_pool_v1_leaf_salt(hash,context,tag,index as u32).map_err(|_|Error::Semantic)?);
    }
    Ok(PrivateSalts::new(salts))
}

fn prove_from_semantics(public:Public<'_>,variant:Variant,hash:HashFn,backend:Backend,sem:BuiltSemantics<LegacyHashFn>,salts:Option<(&ReservedStateOnlyAttemptSecrets,StateOnlyHidingContext)>)->Result<Vec<u8>,Error> {
    let coefficients:Vec<Message<E>>=backend.messages.iter().map(|m|variant.coefficients(m)).collect();
    let z1=Point{x:E::from_qm31(sem.z[1].x),y:E::from_qm31(sem.z[1].y)};
    let y1=encoded(coefficients.iter().map(|m|r0::encoder::eval_message(m,z1)));
    let mut t=Transcript::new(LegacyHashFn(hash),sem.transcript.state(),variant);
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
    #[cfg(feature="r1p-check")]
    let mut alpha1_drawn=E::ZERO;
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
        let alpha1=t.scalar(30,&payload,false);
        #[cfg(feature="r1p-check")]
        {alpha1_drawn=alpha1;}
        fold(&q1,alpha1,false)
    }else{q1};
    let fbytes=encoded(final_message.iter().copied());let row=if variant.folds()==1 {30}else{31};
    let queries=t.queries(row,&fbytes)?;let _rho=t.scalar_k(row+1,&[]);
    // LOG D38.3: every challenge P_R1 reads is now drawn and no proof byte
    // exists yet. A rejected attempt returns only `Error::Rejected`.
    #[cfg(feature="r1p-check")]
    public_check(variant,&R1PublicChallenges{
        alpha:sem.alpha,z:[[sem.z[0].x,sem.z[0].y],[sem.z[1].x,sem.z[1].y]],
        gamma,kappa,alpha0,alpha1:alpha1_drawn,queries:queries.to_vec(),
    },sem.roots[0])?;
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

// ---------------------------------------------------------------------------
// LOG D38.3 / D41.3 / D45.5 R-retry: the prover-side P_R1 check and the capped
// retry loop. The check is the extracted C3 checker (D57) behind z9e's
// public-data and certificate construction; it reads public challenges only.

/// The attempt cap N of the retry loop (D38.3, accepted N = 8).
pub const ATTEMPT_CAP: usize = 8;

#[cfg(all(feature="r1p-check", not(feature="private-leaf-salts")))]
compile_error!("the P_R1 retry loop requires `private-leaf-salts` (LOG D38.3)");

#[cfg(feature="r1p-check")]
pub use aspis_z4b_probe::{R1CheckTimes, R1PublicChallenges};

#[cfg(feature="r1p-check")]
std::thread_local! {
    static CHECK_TIMES: core::cell::RefCell<Vec<R1CheckTimes>> = const { core::cell::RefCell::new(Vec::new()) };
}

/// Durations of the P_R1 checks run on this thread since the last call.
/// Only durations are kept: never a verdict's reason, a challenge or a root.
#[cfg(feature="r1p-check")]
pub fn take_check_times() -> Vec<R1CheckTimes> {
    CHECK_TIMES.with(|v| core::mem::take(&mut *v.borrow_mut()))
}

/// P_R1 on one attempt. R1 is variant S2; P_R1 is not defined for the others.
#[cfg(feature="r1p-check")]
fn public_check(variant:Variant,challenges:&R1PublicChallenges,c1_root:[u8;32])->Result<(),Error> {
    if variant!=Variant::S2 { return Err(Error::Semantic); }
    #[cfg(test)]
    if let Some(accepted)=test_hooks::forced_verdict(c1_root) {
        return if accepted {Ok(())} else {Err(Error::Rejected)};
    }
    let _=c1_root;
    let (accepted,times)=aspis_z4b_probe::p_r1_check(challenges);
    CHECK_TIMES.with(|v| v.borrow_mut().push(times));
    if accepted {Ok(())} else {Err(Error::Rejected)}
}

/// One published proof from the retry loop.
#[cfg(feature="r1p-check")]
pub struct RetriedProof { pub proof:Vec<u8>, pub audit:MaskedFixtureAudit, pub attempts:usize }

/// D38.3 retry loop with fresh OS attempt secrets for every attempt.
#[cfg(feature="r1p-check")]
pub fn prove_masked_retrying(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    nonce_store:&mut DurableStateOnlyMaskNonceStore,
)->Result<RetriedProof,Error> {
    prove_masked_retrying_with(public,compiled,variant,hash,nonce_store,|_|StateOnlyAttemptSecrets::generate().map_err(|_|Error::Entropy))
}

/// D38.3 retry loop. `next_attempt(k)` must return fresh OS-generated secrets
/// for attempt k; a client that binds the nonce to the proof-account address
/// (D38.4) generates a fresh account keypair per attempt and calls
/// `StateOnlyAttemptSecrets::generate_for_mask_nonce` with its public key.
///
/// Each attempt durably burns its nonce in `nonce_store` before any mask or
/// salt is derived (`reserve_and_build_…`). As in Lean `realGameP`
/// (R1Z/GamesR1P.lean:184: accept on `P ∧ VR1 ∧ ¬ exh`), an attempt is
/// rejected when its challenges fail P_R1, when χ is a LogUp pole (`¬ VR1`,
/// LOG D40.3, D73.4.1), or when its mask decode is exhausted (`exh`,
/// D73.4.2). Each returns the same detail-free `Error::Rejected` before any
/// proof byte exists; its secrets are dropped (zeroized), it consumes one of
/// the `ATTEMPT_CAP` attempts, and nothing about it is returned or logged.
/// After `ATTEMPT_CAP` rejections the result is `AttemptsExhausted` and
/// nothing is published (Lean's fixed `failView`, R1Z/GamesR1P.lean:185).
/// Any other error aborts.
#[cfg(feature="r1p-check")]
pub fn prove_masked_retrying_with(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    nonce_store:&mut DurableStateOnlyMaskNonceStore,
    mut next_attempt:impl FnMut(usize)->Result<StateOnlyAttemptSecrets,Error>,
)->Result<RetriedProof,Error> {
    if variant!=Variant::S2 { return Err(Error::Semantic); }
    for k in 0..ATTEMPT_CAP {
        let attempt=next_attempt(k)?;
        match prove_masked_attempt(public,compiled,variant,hash,attempt,nonce_store) {
            Ok((proof,audit))=>return Ok(RetriedProof{proof,audit,attempts:k+1}),
            Err(Error::Rejected)=>continue,
            Err(e)=>return Err(e),
        }
    }
    Err(Error::AttemptsExhausted)
}

/// Test-only injection (cfg(test)): a queue of forced P_R1 verdicts, and a
/// per-attempt record of public/derived freshness witnesses.
#[cfg(all(test,feature="r1p-check"))]
pub(crate) mod test_hooks {
    use alloc::{collections::VecDeque,vec::Vec};
    use aspis_core::{HashFn,field::QM31};
    #[derive(Clone,Debug,Default)]
    pub struct Attempt {
        pub mask_nonce:[u8;32],
        /// Digest of the G mask column (a function of the field-mask entropy).
        pub g_digest:[u8;32],
        /// Digest of the first private C1 leaf salt (a function of the leaf-salt seed).
        pub salt_digest:[u8;32],
        pub c1_root:Option<[u8;32]>,
        pub forced_verdict:Option<bool>,
        /// The pole hook fired on this attempt (no P_R1 check ran).
        pub pole:bool,
        /// The mask-exhaustion hook fired on this attempt (nothing derived).
        pub exhausted:bool,
    }
    std::thread_local! {
        static VERDICTS: core::cell::RefCell<Option<VecDeque<bool>>> = const { core::cell::RefCell::new(None) };
        static ATTEMPTS: core::cell::RefCell<Vec<Attempt>> = const { core::cell::RefCell::new(Vec::new()) };
        /// 1-based attempt numbers on which the Lean `NoPole` test is forced false.
        static POLES: core::cell::RefCell<Vec<usize>> = const { core::cell::RefCell::new(Vec::new()) };
        /// 1-based attempt numbers whose mask decode is forced exhausted.
        static EXHAUST: core::cell::RefCell<Vec<usize>> = const { core::cell::RefCell::new(Vec::new()) };
    }
    pub fn force_poles(attempts:&[usize]) { POLES.with(|p| *p.borrow_mut()=attempts.to_vec()); }
    pub fn force_exhaustion(attempts:&[usize]) { EXHAUST.with(|p| *p.borrow_mut()=attempts.to_vec()); }
    /// Called from `host_semantic::no_pole` after `observe_secrets` recorded
    /// the current attempt.
    pub(crate) fn forced_pole()->bool {
        let k=ATTEMPTS.with(|a| a.borrow().len());
        let hit=POLES.with(|p| p.borrow().contains(&k));
        if hit { ATTEMPTS.with(|a| if let Some(last)=a.borrow_mut().last_mut() {last.pole=true;}); }
        hit
    }
    /// Called right after the nonce reservation, before `observe_secrets`.
    pub(crate) fn forced_exhaustion(mask_nonce:[u8;32])->bool {
        let k=ATTEMPTS.with(|a| a.borrow().len())+1;
        let hit=EXHAUST.with(|p| p.borrow().contains(&k));
        if hit { ATTEMPTS.with(|a| a.borrow_mut().push(Attempt{mask_nonce,exhausted:true,..Attempt::default()})); }
        hit
    }
    pub fn force(verdicts:&[bool]) {
        VERDICTS.with(|v| *v.borrow_mut()=Some(verdicts.iter().copied().collect()));
        ATTEMPTS.with(|a| a.borrow_mut().clear());
    }
    pub fn clear() {
        VERDICTS.with(|v| *v.borrow_mut()=None);
        ATTEMPTS.with(|a| a.borrow_mut().clear());
        POLES.with(|p| p.borrow_mut().clear());
        EXHAUST.with(|p| p.borrow_mut().clear());
    }
    pub fn attempts()->Vec<Attempt> { ATTEMPTS.with(|a| a.borrow().clone()) }
    pub(crate) fn observe_secrets(hash:HashFn,mask_nonce:[u8;32],g:&[QM31;1024],salt0:&[u8;32]) {
        let mut bytes=Vec::with_capacity(16*1024);
        for x in g { let mut b=[0;16];x.write_le_bytes(&mut b);bytes.extend_from_slice(&b); }
        let record=Attempt{mask_nonce,g_digest:hash(&[b"test:g",&bytes]),salt_digest:hash(&[b"test:salt0",salt0]),..Attempt::default()};
        ATTEMPTS.with(|a| a.borrow_mut().push(record));
    }
    pub(crate) fn forced_verdict(c1_root:[u8;32])->Option<bool> {
        let verdict=VERDICTS.with(|v| v.borrow_mut().as_mut().map(|q| q.pop_front().unwrap_or(true)))?;
        ATTEMPTS.with(|a| if let Some(last)=a.borrow_mut().last_mut() {last.c1_root=Some(c1_root);last.forced_verdict=Some(verdict);});
        Some(verdict)
    }
}

#[cfg(all(test,feature="r1p-check"))]
#[path="prover_retry_tests.rs"]
mod retry_tests;
