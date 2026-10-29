//! UNPROVED COST PROBE. Own native prover, including D14 content.
use alloc::{vec,vec::Vec};
use aspis_core::{digest::LegacyHashFn,HashFn,field::{WideExact as E,M31,QM31 as K,CM31},r0::{self,CodeField,domain::{Point,FibreIndex},merkle,wire::FibreOpening,Message},state_only_hiding::StateOnlyHidingContext};
use aspis_statement::pool_v1::{pair_forest_semantic_terminal::r0::Public,pair_forest_trace::PoolV1PairForestMergedC1CompilationV1};
use crate::host_forest::pool_v1_pair_forest_copy_active_row_masks_v1;
use aspis_prover::{state_only_entropy::{StateOnlyAttemptSecrets,ReservedStateOnlyAttemptSecrets,DurableStateOnlyMaskNonceStore},state_only_hiding::{apply_pool_v1_pair_forest_mask_material_v1,InMemoryStateOnlyMaskNonceStore,StateOnlyMaskBuildError,StateOnlyMaskNonceStore}};
use crate::{transport::Variant,verifier::{Error},host_weights::{Weights,QUARTER,PERM},host_transcript::Transcript,host_commitment::{Commitment,CommitmentTime,EncodingDomain,PrivateSalts},host_semantic::{BuiltSemantics,Commitments},r1_wire::Error as SError};
/// Host commitment backend. Adopted format (PREREG-PROOF-SIZE-2): salted
/// leaves under binary trees; there is no unsalted or eight-way commitment.
pub struct Backend {pub hash:HashFn,pub variant:Variant,pub domain:EncodingDomain,pub messages:Vec<Message<E>>,pub c1:Option<Commitment>,pub c2:Option<Commitment>,c1_salts:Option<crate::host_commitment::PrivateSalts>,c2_salts:Option<crate::host_commitment::PrivateSalts>}
impl Commitments for Backend {
    fn c1(&mut self,columns:&[Vec<M31>;26],d:&[K;1024])->Result<[u8;32],SError>{
        let mut lane=0;
        while lane<26 {
            let mut row=0;
            while row<1024 {self.messages[lane][row]=E::from_m31(columns[lane][row]);row+=1;}
            lane+=1;
        }
        let mut row=0;
        while row<1024 {self.messages[28][row]=E::from_qm31(d[row]);row+=1;}

        let salts=self.c1_salts.take().ok_or(SError::Public)?;
        let c=Commitment::new_salted(self.hash,&self.domain,CommitmentTime::C1,&self.messages,self.variant,salts).map_err(|_|SError::Public)?;
        let root=c.root();self.c1=Some(c);Ok(root)
    }
    fn c2(&mut self,h1:&[K],g:&[K;1024])->Result<[u8;32],SError>{
        let mut row=0;
        while row<1024 {self.messages[26][row]=E::from_qm31(h1[row]);row+=1;}
        row=0;
        while row<1024 {self.messages[27][row]=E::from_qm31(g[row]);row+=1;}

        let salts=self.c2_salts.take().ok_or(SError::Public)?;
        let c=Commitment::new_salted(self.hash,&self.domain,CommitmentTime::C2,&self.messages,self.variant,salts).map_err(|_|SError::Public)?;
        let root=c.root();self.c2=Some(c);Ok(root)
    }
}
pub fn round(q:&[E],w:&[E])->[E;7] {
    assert_eq!(q.len(),w.len());
    let mut c=[E::ZERO;7];
    let mut d=0;
    while d<q.len()/4 {
        let mut s=0;
        while s<4 {
            let mut t=0;
            while t<4 {
                let at=s+PERM[t];
                c[at]=c[at].add(q[4*d+s].mul(w[4*d+t]));
                t+=1;
            }
            s+=1;
        }
        d+=1;
    }
    let mut i=0;
    while i<7 {c[i]=c[i].mul_m31(QUARTER);i+=1;}
    c
}
pub fn fold(q:&[E],alpha:E,dual:bool)->Vec<E> {
    let mut out=Vec::with_capacity(q.len()/4);
    let mut i=0;
    while i<q.len()/4 {
        let h=[q[4*i],q[4*i+1],q[4*i+2],q[4*i+3]];
        let value=fold_cell(h,alpha,dual);
        out.push(value);i+=1;
    }
    out
}

#[inline(always)]
fn fold_cell(h:[E;4],alpha:E,dual:bool)->E {
    if dual {
            h[0].add(alpha.mul(h[3].add(alpha.mul(h[2].add(alpha.mul(h[1])))))).mul_m31(QUARTER)
        } else {
            h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
        }
}

/// Ordered byte assembly used by the real pipeline; each field encoding is a leaf.
fn encoded_slice(values:&[E])->Vec<u8> {
    let mut out=Vec::with_capacity(32*values.len());
    let mut i=0;
    while i<values.len() {out.extend_from_slice(&values[i].to_le_bytes());i+=1;}
    out
}

pub fn encoded(values:impl IntoIterator<Item=E>)->Vec<u8> {values.into_iter().flat_map(E::to_le_bytes).collect()}

/// Deterministic fixture-only rejection sampling of K limbs. No distribution
/// property is inferred from these fixed test samples.
#[cfg(feature="insecure-spend-fixture")]
fn tail_samples(hash:HashFn,seed:&[u8;32])->[K;56] {
    let mut counter=0u64;
    let mut limb=||loop {
        let b=hash(&[b"UNPROVED:R1:P2:fixture-tail",seed,&counter.to_le_bytes()]);counter+=1;
        let x=u32::from_le_bytes(b[..4].try_into().unwrap())&0x7fffffff;
        if x<aspis_core::field::P {break M31(x);}
    };
    core::array::from_fn(|_|K{c0:CM31::new(limb(),limb()),c1:CM31::new(limb(),limb())})
}
/// Convenience API, deliberately fixture-only: it always emits a fully masked
/// P3 proof in the adopted compact binary-multiproof format.
#[cfg(feature="insecure-spend-fixture")]
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

#[cfg(feature="insecure-spend-fixture")]
fn fixture_secret(hash:HashFn,domain:&[u8],seed:&[u8;32],public:&[u8],variant:Variant)->Result<[u8;32],Error> {
    let mut value=hash(&[domain,seed,public,&[variant.tag()]]);
    if value==[0;32] { return Err(Error::Semantic); }
    Ok(value)
}

fn inactive_sum_m31(values:&[M31],masks:&[u16;64])->M31 {
    let mut sum=M31::ZERO;
    let mut row=0;
    while row<values.len() {
        if masks[row>>4]&(1<<(row&15))==0 {sum=sum.add(values[row]);}
        row+=1;
    }
    sum
}

fn inactive_sum_k(values:&[K],masks:&[u16;64])->K {
    let mut sum=K::ZERO;
    let mut row=0;
    while row<values.len() {
        if masks[row>>4]&(1<<(row&15))==0 {sum=sum.add(values[row]);}
        row+=1;
    }
    sum
}

/// Deterministic, insecure masked fixture path. Its derivations exist only for
/// reproducible local cost experiments and are not production entropy.
#[cfg(feature="insecure-spend-fixture")]
pub fn prove_masked_fixture(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    fixture_seed:&[u8;32],
)->Result<(Vec<u8>,MaskedFixtureAudit),Error> {
    let public_bytes=crate::host_public::materialize_public_bytes(public).map_err(|_|Error::Semantic)?;
    let context=StateOnlyHidingContext::pool_v1_pair_forest_v1(hash(&[&public_bytes]),fixture_secret(hash,b"UNPROVED:R1:fixture-mask-nonce",fixture_seed,&public_bytes,variant)?);
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
pub fn prove_masked_attempt(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    attempt:StateOnlyAttemptSecrets,
    nonce_store:&mut DurableStateOnlyMaskNonceStore,
)->Result<(Vec<u8>,MaskedFixtureAudit),Error> {
    let public_bytes=crate::host_public::materialize_public_bytes(public).map_err(|_|Error::Semantic)?;
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
    let g=fixed_k_column(&applied.g);
    let h1_padding=fixed_k_column(&applied.h1_padding);
    let audit=audit_masks(&noised_c1.c1,&applied.mask_only_c1,&d,&g,&h1_padding,&masks);
    if audit.c1_columns_inactive_balanced!=16
        || audit.mask_only_columns_inactive_balanced!=10
        || !audit.d_inactive_balanced
        || !audit.g_inactive_balanced
        || !audit.h1_padding_inactive_balanced
    { return Err(Error::Semantic); }
    let (c1_salts,c2_salts)=(Some(derive_private_salts(&reserved,context,hash,merkle::C1_TAG)?),Some(derive_private_salts(&reserved,context,hash,merkle::C2_TAG)?));
    #[cfg(all(test,feature="r1p-check"))]
    test_hooks::observe_secrets(hash,reserved.mask_nonce(),&g,c1_salts.as_ref().unwrap().get(0));
    let mut backend=Backend{hash,variant,domain:EncodingDomain::new().map_err(|_|Error::Allocation)?,messages:vec![[E::ZERO;1024];29],c1:None,c2:None,c1_salts,c2_salts};
    let sem=crate::host_semantic::build_with_material(public,compiled,&noised_c1,&applied.mask_only_c1,&d,&g,&h1_padding,&mut backend,LegacyHashFn(hash),variant).map_err(semantic_error)?;
    let h1_total_balanced=crate::prover_helper_sum::state_only_copy_helper_sum(&sem.columns[26])==Some(K::ZERO);
    if !h1_total_balanced { return Err(Error::Semantic); }
    let audit=MaskedFixtureAudit{h1_total_balanced,..audit};
    let proof=prove_from_semantics(public,variant,hash,backend,sem,(&reserved,context))?;
    Ok((proof,audit))
}

/// Fixed-size copy with no closure retaining a material-owner loan.
fn fixed_k_column(values:&[K])->[K;1024] {
    let mut out=[K::ZERO;1024];
    let mut i=0;
    while i<1024 {out[i]=values[i];i+=1;}
    out
}
fn audit_masks(c1:&[Vec<M31>],mask_only:&[Vec<M31>;10],d:&[K;1024],g:&[K;1024],h1_padding:&[K;1024],masks:&[u16;64])->MaskedFixtureAudit {
    let mut c1_columns_inactive_balanced=0;
    let mut column=0;
    while column<c1.len() {
        if inactive_sum_m31(&c1[column],masks)==M31::ZERO {c1_columns_inactive_balanced+=1;}
        column+=1;
    }
    let mut mask_only_columns_inactive_balanced=0;
    column=0;
    while column<10 {
        if inactive_sum_m31(&mask_only[column],masks)==M31::ZERO {mask_only_columns_inactive_balanced+=1;}
        column+=1;
    }
    MaskedFixtureAudit{
        c1_columns_inactive_balanced,
        mask_only_columns_inactive_balanced,
        d_inactive_balanced:inactive_sum_k(d,masks)==K::ZERO,
        g_inactive_balanced:inactive_sum_k(g,masks)==K::ZERO,
        h1_padding_inactive_balanced:inactive_sum_k(h1_padding,masks)==K::ZERO,
        h1_total_balanced:true,
    }

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

fn derive_private_salts(reserved:&ReservedStateOnlyAttemptSecrets,context:StateOnlyHidingContext,hash:HashFn,tag:u8)->Result<PrivateSalts,Error> {
    let count=aspis_core::r0::FIBRE_COUNT;

    let mut salts=Vec::new();salts.try_reserve_exact(aspis_core::r0::FIBRE_COUNT).map_err(|_|Error::Allocation)?;
    let mut result=Ok(salts);
    let mut index=0usize;
    while index<count {
        result=match result {
            Ok(salts)=>derive_private_salt_step(reserved,context,hash,tag,index as u32,salts),
            Err(error)=>Err(error),
        };
        index+=1;
    }
    result.map(PrivateSalts::new)
}

/// The R1 proof (PREREG-PROOF-SIZE-2, adopted 2026-10-19): binary trees (C1/C2
/// built by the Backend, the padded folded tree here) and the fixed-length
/// compact stored format of `crate::compact` (57,607 bytes). Every transcript
/// message is the logical byte string of the retired eight-way format; only
/// the roots (binary trees) and the stored encoding differ. R1 is variant S2.
/// Owned result of rows 27–29. No transcript loan or iterator survives a phase.
struct PreparedOpening {
    backend:Backend,
    sem:BuiltSemantics<LegacyHashFn>,
    transcript:Transcript<LegacyHashFn>,
    y1:Vec<u8>,
    gamma:E,
    inactive:E,
    kappa:E,
    alpha0:E,
    c0bytes:Vec<u8>,
    q1:Vec<E>,
    w1:Vec<E>,
    folded_word:Vec<E>,
}

// Match frozen weights::box_from_parts' allocation boundary. Keep Box/Drop
// outside the owned extraction kernel and retain the caller's final drop.
#[inline(never)]
pub(crate) fn retain_weights_box(w:Weights)->alloc::boxed::Box<Weights> {
    const _: () = {
        assert!(core::mem::size_of::<Weights>() == core::mem::size_of::<crate::weights::Weights>());
        assert!(core::mem::align_of::<Weights>() == core::mem::align_of::<crate::weights::Weights>());
    };
    alloc::boxed::Box::new(w)
}

fn prepare_opening(variant:Variant,hash:HashFn,backend:Backend,sem:BuiltSemantics<LegacyHashFn>)->Result<PreparedOpening,Error> {
    if variant!=Variant::S2 {return Err(Error::Semantic);}
    let coefficients=opening_coefficients(variant,&backend.messages);
    let z1=Point{x:E::from_qm31(sem.z[1].x),y:E::from_qm31(sem.z[1].y)};
    let y1=opening_claim_bytes(&coefficients,z1);
    let mut transcript=Transcript::new(LegacyHashFn(hash),sem.transcript.state(),variant);
    let gamma=transcript.scalar(27,&y1,true);
    let q=opening_batch(&coefficients,gamma);
    let w=retain_weights_box(Weights::new(variant,&sem.alpha,&sem.z)?);
    let inactive=opening_inactive(&q,&w);
    let kappa=transcript.scalar(28,&inactive.to_le_bytes(),false);
    let mut weights=match aspis_core::r0::heap::filled(1024,E::ZERO) { Ok(v)=>v, Err(_)=>return Err(Error::Allocation) };
    w.materialize(kappa,weights.as_mut_slice().try_into().unwrap())?;
    let c0=round(&q,&weights);
    let c0bytes=encoded_slice(&c0);
    let alpha0=transcript.scalar(29,&c0bytes,false);
    let q1=fold(&q,alpha0,false);
    let w1=fold(&weights,alpha0,true);
    let folded_word=backend.domain.evaluate(&q1,0).map_err(|_|Error::Allocation)?;
    Ok(PreparedOpening{backend,sem,transcript,y1,gamma,inactive,kappa,alpha0,c0bytes,q1,w1,folded_word})
}

/// Coefficient permutation is a small unchanged leaf; the vector owner is here.
fn opening_coefficients(variant:Variant,messages:&[Message<E>])->Vec<Message<E>> {
    let mut coefficients=Vec::with_capacity(messages.len());
    let mut lane=0;
    while lane<messages.len() {let column=variant.coefficients(&messages[lane]);coefficients.push(column);lane+=1;}
    coefficients
}
fn opening_claim_bytes(coefficients:&[Message<E>],z1:Point<E>)->Vec<u8> {
    let mut bytes=Vec::with_capacity(32*coefficients.len());
    let mut lane=0;
    while lane<coefficients.len() {
        let value=r0::encoder::eval_message(&coefficients[lane],z1);
        bytes.extend_from_slice(&value.to_le_bytes());lane+=1;
    }
    bytes
}
fn opening_batch(coefficients:&[Message<E>],gamma:E)->Vec<E> {
    let gp=crate::prover_powers::powers::<29>(gamma);
    let mut q=Vec::with_capacity(1024);let mut row=0;
    while row<1024 {let value=opening_row(coefficients,&gp,row);q.push(value);row+=1;}
    q
}
#[inline(always)]
fn opening_row(coefficients:&[Message<E>],gp:&[E;29],row:usize)->E {
    let mut value=E::ZERO;let mut lane=0;
    while lane<29 {value=value.add(gp[lane].mul(coefficients[lane][row]));lane+=1;}
    value
}
fn opening_inactive(q:&[E],w:&Weights)->E {
    let mut inactive=E::ZERO;
    let mut row=0;
    while row<1024 {inactive=inactive.add(q[row].mul_qm31(w.raw(0,row)));row+=1;}
    inactive
}

/// Owned input to the publication phase. Constructed only after P_R1 accepts.
struct Publication {
    backend:Backend,
    semantic_bytes:Vec<u8>,
    y1:Vec<u8>,
    inactive:E,
    c0bytes:Vec<u8>,
    root:[u8;32],
    c1bytes:Vec<u8>,
    fbytes:Vec<u8>,
    queries:[u32;22],
    folded_word:Vec<E>,
    folded_salts:PrivateSalts,
    tree:crate::host_tree::BinaryTree,
}

fn folded_leaves(hash:HashFn,word:&[E],salts:&PrivateSalts)->Vec<[u8;32]> {
    let mut leaves=Vec::with_capacity(1<<18);
    let mut u=0;
    while u<1<<18 {
        let mut values=[0u8;128];
        if u<1<<16 {
            let mut s=0;
            while s<4 {
                values[32*s..32*(s+1)].copy_from_slice(&word[4*u+s].to_le_bytes());
                s+=1;
            }
        }
        let leaf=aspis_core::state_only_private_merkle::private_leaf_hash(hash,0x72,&values,salts.get(u));
        leaves.push(leaf);
        u+=1;
    }
    leaves
}

fn finish_opening(variant:Variant,hash:HashFn,prepared:PreparedOpening,folded_salts:PrivateSalts)->Result<Publication,Error> {
    let PreparedOpening{backend,sem,mut transcript,y1,gamma,inactive,kappa,alpha0,c0bytes,q1,w1,folded_word}=prepared;
    let leaves=folded_leaves(hash,&folded_word,&folded_salts);
    let tree=crate::host_tree::BinaryTree::new(LegacyHashFn(hash),leaves).ok_or(Error::Allocation)?;
    let root=tree.root();
    let c1=round(&q1,&w1);
    let c1bytes=encoded_slice(&c1);
    let mut payload=root.to_vec();payload.extend_from_slice(&c1bytes);
    let alpha1=transcript.scalar(30,&payload,false);
    let final_message=fold(&q1,alpha1,false);
    let fbytes=encoded_slice(&final_message);
    let queries=transcript.queries(31,&fbytes)?;
    let _rho=transcript.scalar_k(32,&[]);
    #[cfg(feature="r1p-check")]
    public_check(variant,&R1PublicChallenges{
        alpha:sem.alpha,z:[[sem.z[0].x,sem.z[0].y],[sem.z[1].x,sem.z[1].y]],
        gamma,kappa,alpha0,alpha1,queries:queries.to_vec(),
    },sem.roots[0])?;
    Ok(Publication{backend,semantic_bytes:sem.bytes,y1,inactive,c0bytes,root,c1bytes,fbytes,
        queries,folded_word,folded_salts,tree})
}

/// Counted insertion and dedup on at most 22 public query indices. Sorting is
/// explicit so publication does not depend on an opaque standard sort adapter.
fn publication_indices(queries:&[u32;22],begin:usize,end:usize,folded:bool)->Vec<u32> {
    let mut out=Vec::with_capacity(end-begin);
    let mut i=begin;
    while i<end {
        let value=if folded {queries[i]/4} else {queries[i]};
        let mut at=0;
        while at<out.len() && out[at]<value {at+=1;}
        if at==out.len() || out[at]!=value {out.insert(at,value);}
        i+=1;
    }
    out
}

fn publish_compact(variant:Variant,p:Publication)->Result<Vec<u8>,Error> {
    use crate::host_compact as compact;
    let Publication{mut backend,semantic_bytes,y1,inactive,c0bytes,root,c1bytes,fbytes,
        queries,folded_word,folded_salts,tree}=p;
    let mut out=Vec::with_capacity(compact::PROOF_BYTES);
    out.extend_from_slice(compact::MAGIC);
    out.extend_from_slice(&[variant.tag(),0,0,0,0,0,0,0]);
    compact::compact_semantic(&semantic_bytes,&mut out).map_err(|_|Error::Semantic)?;
    compact::compact_values(&y1,&mut out).map_err(|_|Error::Semantic)?;
    out.extend_from_slice(&inactive.to_le_bytes());out.extend_from_slice(&c0bytes);
    out.extend_from_slice(&root);out.extend_from_slice(&c1bytes);out.extend_from_slice(&fbytes);
    assert_eq!(out.len(),compact::OFF_OPENINGS);
    let cc1=backend.c1.take().unwrap();
    let cc2=backend.c2.take().unwrap();
    out=append_query_openings(out,&cc1,&cc2,&queries,&folded_word,&folded_salts);
    assert_eq!(out.len(),compact::OFF_NODES);
    out=append_node_slots(out,&cc1,&cc2,&tree,&queries)?;
    assert_eq!(out.len(),compact::PROOF_BYTES);
    Ok(out)
}

fn append_node_slots(out:Vec<u8>,cc1:&Commitment,cc2:&Commitment,tree:&crate::host_tree::BinaryTree,queries:&[u32;22])->Result<Vec<u8>,Error> {
    let out=append_node_slot(out,cc1,cc2,tree,queries,0,0)?;
    let out=append_node_slot(out,cc1,cc2,tree,queries,0,1)?;
    let out=append_node_slot(out,cc1,cc2,tree,queries,0,2)?;
    let out=append_node_slot(out,cc1,cc2,tree,queries,1,0)?;
    let out=append_node_slot(out,cc1,cc2,tree,queries,1,1)?;
    append_node_slot(out,cc1,cc2,tree,queries,1,2)
}
fn append_node_slot(mut out:Vec<u8>,cc1:&Commitment,cc2:&Commitment,tree:&crate::host_tree::BinaryTree,queries:&[u32;22],batch:usize,t:usize)->Result<Vec<u8>,Error> {
    use crate::compact;
    let begin=if batch==0 {0} else {compact::SPLIT};
    let end=if batch==0 {compact::SPLIT} else {22};
    let idx=publication_indices(queries,begin,end,t==2);
    let nodes=match t {0=>cc1.multiproof(&idx),1=>cc2.multiproof(&idx),_=>tree.multiproof(&idx)}.ok_or(Error::Allocation)?;
    let cap=32*compact::SLOT_NODES[3*batch+t];
    assert!(nodes.len()<=cap);
    out.extend_from_slice(&nodes);
    let padded=out.len()+cap-nodes.len();
    out.resize(padded,0);
    Ok(out)
}

/// The query loop carries only the output buffer and immutable opening data.
fn append_query_openings(mut out:Vec<u8>,cc1:&Commitment,cc2:&Commitment,queries:&[u32;22],folded_word:&[E],folded_salts:&PrivateSalts)->Vec<u8> {
    let mut i=0;
    while i<22 {
        let u=FibreIndex::new(queries[i] as usize).unwrap();
        let mut opening=FibreOpening{values:[[E::ZERO;29];4],paths:[[[[0;32];7];6];2]};
        cc1.fill_opening(u,&mut opening);cc2.fill_opening(u,&mut opening);
        out=append_opening_values(out,opening);
        out.extend_from_slice(cc1.opening_salt(u).unwrap());
        out.extend_from_slice(cc2.opening_salt(u).unwrap());
        let at=4*(u.get()/4);
        let values=encoded_slice(&folded_word[at..at+4]);
        out.extend_from_slice(&values);
        out.extend_from_slice(folded_salts.get(u.get()/4));
        i+=1;
    }
    out
}

/// No commitment or publication loan enters this nested byte-assembly loop.
fn append_opening_values(out:Vec<u8>,opening:FibreOpening)->Vec<u8> {
    let out=append_opening_base_row(out,&opening.values[0]);
    let out=append_opening_base_row(out,&opening.values[1]);
    let out=append_opening_base_row(out,&opening.values[2]);
    let out=append_opening_base_row(out,&opening.values[3]);
    let out=append_opening_secure_row(out,&opening.values[0]);
    let out=append_opening_secure_row(out,&opening.values[1]);
    let out=append_opening_secure_row(out,&opening.values[2]);
    append_opening_secure_row(out,&opening.values[3])
}
fn append_opening_base_row(mut out:Vec<u8>,row:&[E;29])->Vec<u8> {
    let mut lane=0;
    while lane<26 {
        let bytes=row[lane].to_le_bytes();out.extend_from_slice(&bytes[..4]);lane+=1;
    }
    let bytes=row[28].to_le_bytes();out.extend_from_slice(&bytes[..16]);
    out
}
fn append_opening_secure_row(mut out:Vec<u8>,row:&[E;29])->Vec<u8> {
    let mut lane=26;
    while lane<28 {
        let bytes=row[lane].to_le_bytes();out.extend_from_slice(&bytes[..16]);lane+=1;
    }
    out
}

fn prove_from_semantics(public:Public<'_>,variant:Variant,hash:HashFn,backend:Backend,sem:BuiltSemantics<LegacyHashFn>,salts:(&ReservedStateOnlyAttemptSecrets,StateOnlyHidingContext))->Result<Vec<u8>,Error> {
    let _=public;
    let prepared=prepare_opening(variant,hash,backend,sem)?;
    let (reserved,context)=salts;
    let folded_salts=derive_private_salts(reserved,context,hash,0x72)?;
    let publication=finish_opening(variant,hash,prepared,folded_salts)?;
    publish_compact(variant,publication)
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
    #[cfg(not(feature="ct-host-prover"))] static CHECK_TIMES: core::cell::RefCell<Vec<R1CheckTimes>> = const { core::cell::RefCell::new(Vec::new()) };
}

/// Durations of the P_R1 checks run on this thread since the last call.
/// Only durations are kept: never a verdict's reason, a challenge or a root.
#[cfg(feature="r1p-check")]
pub fn take_check_times() -> Vec<R1CheckTimes> {
    #[cfg(not(feature="ct-host-prover"))] { CHECK_TIMES.with(|v| core::mem::take(&mut *v.borrow_mut())) } #[cfg(feature="ct-host-prover")] { Vec::new() }
}

/// P_R1 on one attempt. R1 is variant S2; P_R1 is not defined for the others.
#[cfg(feature="r1p-check")]
fn public_check(variant:Variant,challenges:&R1PublicChallenges,c1_root:[u8;32])->Result<(),Error> {
    if variant!=Variant::S2 { return Err(Error::Semantic); }
    #[cfg(test)]
    test_hooks::observe_challenges(challenges);
    #[cfg(test)]
    if let Some(accepted)=test_hooks::forced_verdict(c1_root) {
        return if accepted {Ok(())} else {Err(Error::Rejected)};
    }
    let _=c1_root;
    let (accepted,times)=aspis_z4b_probe::p_r1_check(challenges);
    #[cfg(not(feature="ct-host-prover"))] CHECK_TIMES.with(|v| v.borrow_mut().push(times)); #[cfg(feature="ct-host-prover")] let _ = times;
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
    next_attempt:impl FnMut(usize)->Result<StateOnlyAttemptSecrets,Error>,
)->Result<RetriedProof,Error> {
    if variant!=Variant::S2 { return Err(Error::Semantic); }
    retry_attempt(public,compiled,variant,hash,nonce_store,next_attempt,0)
}

fn retry_attempt(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    nonce_store:&mut DurableStateOnlyMaskNonceStore,
    mut next_attempt:impl FnMut(usize)->Result<StateOnlyAttemptSecrets,Error>,
    k:usize,
)->Result<RetriedProof,Error> {
    if k>=ATTEMPT_CAP { return Err(Error::AttemptsExhausted); }
    let attempt=next_attempt(k)?;
    match prove_masked_attempt(public,compiled,variant,hash,attempt,nonce_store) {
        Ok((proof,audit))=>Ok(RetriedProof{proof,audit,attempts:k+1}),
        Err(Error::Rejected)=>retry_attempt(public,compiled,variant,hash,nonce_store,next_attempt,k+1),
        Err(e)=>Err(e),
    }
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
    #[cfg(feature="r1p-check")]
    std::thread_local! {
        static CHALLENGES: core::cell::RefCell<Vec<super::R1PublicChallenges>> = const { core::cell::RefCell::new(Vec::new()) };
    }
    /// Test builds only (LOG D72.2 column audit): the challenges of each P_R1 check on this thread.
    #[cfg(feature="r1p-check")]
    pub(crate) fn observe_challenges(ch:&super::R1PublicChallenges) { CHALLENGES.with(|c| c.borrow_mut().push(ch.clone())); }
    #[cfg(feature="r1p-check")]
    pub fn take_challenges()->Vec<super::R1PublicChallenges> { CHALLENGES.with(|c| core::mem::take(&mut *c.borrow_mut())) }
    pub(crate) fn forced_verdict(c1_root:[u8;32])->Option<bool> {
        let verdict=VERDICTS.with(|v| v.borrow_mut().as_mut().map(|q| q.pop_front().unwrap_or(true)))?;
        ATTEMPTS.with(|a| if let Some(last)=a.borrow_mut().last_mut() {last.c1_root=Some(c1_root);last.forced_verdict=Some(verdict);});
        Some(verdict)
    }
}

#[cfg(all(test,feature="r1p-check"))]
#[path="prover_retry_tests.rs"]
mod retry_tests;

fn derive_private_salt_step(reserved:&ReservedStateOnlyAttemptSecrets,context:StateOnlyHidingContext,hash:HashFn,tag:u8,index:u32,mut salts:Vec<[u8;32]>)->Result<Vec<[u8;32]>,Error> {
    let salt=reserved.derive_pool_v1_leaf_salt(hash,context,tag,index).map_err(|_|Error::Semantic)?;
    salts.push(salt);
    Ok(salts)
}

#[cfg(kani)]
mod pdict_rejection_contracts {
    use super::*;
    #[kani::proof]
    fn semantic_rejection_partition() {
        let e = crate::r1_wire::pdict_error_contracts::arbitrary_error();
        let expected = match e { SError::ActivePole => Error::Rejected, _ => Error::Semantic };
        assert_eq!(semantic_error(e),expected);
    }
    #[kani::proof]
    fn mask_rejection_partition() {
        let tag: u8 = kani::any();
        kani::assume(tag < 5);
        let e = match tag {
            0 => StateOnlyMaskBuildError::ZeroPrivateEntropy,
            1 => StateOnlyMaskBuildError::ReusedMaskNonce,
            2 => StateOnlyMaskBuildError::MaskSampleExhausted,
            3 => StateOnlyMaskBuildError::TraceShape,
            _ => StateOnlyMaskBuildError::Layout,
        };
        let expected = match e { StateOnlyMaskBuildError::MaskSampleExhausted => Error::Rejected, _ => Error::Semantic };
        assert_eq!(mask_error(e),expected);
    }
}
