//! UNPROVED COST PROBE. G-sim (LOG D44.3): the explicit, witness-free R1
//! simulator `simE` of R0Z/RefPayload.lean, inside the ideal game of
//! R1Z/GamesR1.lean (`fsR1.ideal`, design zf1/DESIGN-R1-GAMES.txt §5).
//!
//! Input: the public statement only (no compiled trace, no witness) and a
//! 32-byte seed from which every coin of the ideal game is expanded.
//! Per attempt k < N = 8 (the ideal game's capped loop on P alone):
//!   1. coins c_k: the 115 transcript answers, the three roots (C1, C2,
//!      folded) and the commitment answers (salts, leaf, node digests);
//!   2. ch := dec(squeeze answers): the prover's own transcript code is run
//!      with every read answered by the next transcript coin, so the answers
//!      (hence the decoded challenges) do not depend on the payload bytes;
//!   3. P_R1(ch) by the same check as the prover (z9e: emit + extracted C3
//!      checker); rejected → next attempt, exhausted → `AttemptsExhausted`;
//!   4. the uniform tape t: fresh mask material applied to the ZERO trace
//!      (lanes 0..15 eligible noise only, mask-only lanes 16..25, H1 padding
//!      with no helper, G, D): the pure-tape trace τ = tapeLinear(equiv⁻¹ t);
//!   5. the view Ψ_ch(refPayload + L τ) (see `semantic` below);
//!   6. VerLog: the transcript reads are re-run on the view's records with
//!      the same answers and recorded as (address, answer); every opened leaf
//!      read and every node read on the opened paths is programmed with a
//!      coin, the top node's answer being the root coin.
//! Output: the proof bytes and the programmed table. The R1 verifier is then
//! run against `programmed_hash`, which answers programmed addresses from
//! the table and every other address with the real hash.
use crate::host_multilinear::multilinear_evaluate_qm31;
use alloc::{collections::{BTreeMap,BTreeSet},vec,vec::Vec};
use core::cell::RefCell;
use aspis_core::{Digest32,HashFn,circle::SecureCirclePoint,digest::LegacyHashFn,
    field::{WideExact as E,M31,QM31 as K,CM31},
    r0::{CodeField,Message,domain::{self,FibreIndex,Point},encoder::eval_message,fold::phi_inverse,merkle},
    state_only_hiding::{StateOnlyHidingContext,state_only_selected_mask_value},
    state_only_private_merkle::private_leaf_hash_with_digest,
    state_only_sumcheck::{evaluate_state_only_polynomial,state_only_boundary_sum}};
use aspis_statement::{StateOnlyTraceFoundation,pool_v1::pair_forest_semantic_terminal::r0::Public};
use aspis_prover::{HOST_HASH,state_only_entropy::StateOnlyAttemptSecrets,
    state_only_hiding::{apply_pool_v1_pair_forest_mask_material_v1,apply_pool_v1_pair_forest_h1_padding_mask_v1,InMemoryStateOnlyMaskNonceStore}};
use crate::{compact, multiproof,transport::Variant,verifier::Error,host_weights::Weights,transcript::Transcript,
    r1_wire::{self as wire,Challenges,SemanticTranscript},host_semantic::{extra,point_claims},
    prover::{encoded,fold,round,ATTEMPT_CAP,R1PublicChallenges}};

/// Ablations used only to show that the verifier test has teeth: dropping
/// S₀ from the mask-sum cell, or dropping the round-9 terminal shift.
#[doc(hidden)]
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Ablation { None, NoS0, NoShift }

pub type Table = BTreeMap<Vec<u8>,[u8;32]>;

#[derive(Clone,Copy,Debug,Default)]
pub struct SimTimes {
    /// Steps 1–2 (all attempts).
    pub draw: f64,
    /// Step 3, the P_R1 check (all attempts).
    pub p_r1: f64,
    /// Step 4.
    pub tape: f64,
    /// Step 5, semantic part: mask sum, S₀, ten rounds, claims, OOD.
    pub semantic: f64,
    /// Step 5, opening part: y1, inactive, batched rounds, folds, openings.
    pub opening: f64,
    /// Step 6: Merkle programming, serialisation, transcript recording.
    pub program: f64,
    pub total: f64,
}

pub struct Simulated {
    pub proof: Vec<u8>,
    pub table: Table,
    pub attempts: usize,
    pub transcript_reads: usize,
    pub commitment_reads: usize,
    pub times: SimTimes,
}

// ------------------------------------------------------------------ coins
/// Coin expander: coin i of attempt k is H(domain ‖ seed ‖ k ‖ stream ‖ i).
struct Coins { seed:[u8;32], attempt:u32, stream:u8, next:u64 }
impl Coins {
    fn new(seed:[u8;32],attempt:u32,stream:u8)->Self { Self{seed,attempt,stream,next:0} }
    fn coin(&mut self)->[u8;32] {
        let c=HOST_HASH(&[b"UNPROVED:R1:SIM:COIN",&self.seed,&self.attempt.to_le_bytes(),&[self.stream],&self.next.to_le_bytes()]);
        self.next+=1;c
    }
    fn nonzero(&mut self)->[u8;32] { loop { let c=self.coin(); if c!=[0;32] {return c;} } }
}

fn concat(parts:&[&[u8]])->Vec<u8> {
    let mut a=Vec::with_capacity(parts.iter().map(|p|p.len()).sum());
    for p in parts {a.extend_from_slice(p);}
    a
}

/// Answers every read with the next pre-drawn transcript coin; optionally
/// records (address, answer).
struct CoinState { coins:Vec<[u8;32]>, next:usize, record:Option<Table>, collision:bool }
#[derive(Clone,Copy)]
struct CoinOracle<'a>(&'a RefCell<CoinState>);
impl Digest32 for CoinOracle<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        let mut s=self.0.borrow_mut();
        let answer=*s.coins.get(s.next).unwrap_or(&[0;32]);
        s.next+=1;
        if let Some(t)=s.record.as_mut() {
            if let Some(prev)=t.insert(concat(parts),answer) { if prev!=answer {s.collision=true;} }
        }
        answer
    }
}

/// Programs exactly one read: records (address, answer) and returns answer.
#[derive(Clone,Copy)]
struct ProgramOne<'a>{ table:&'a RefCell<(Table,bool)>, answer:[u8;32] }
impl Digest32 for ProgramOne<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        let mut t=self.table.borrow_mut();
        if let Some(prev)=t.0.insert(concat(parts),self.answer) { if prev!=self.answer {t.1=true;} }
        self.answer
    }
}

// --------------------------------------------------- the programmed oracle
std::thread_local! {
    static PROGRAMMED: RefCell<Option<(Table,BTreeSet<Vec<u8>>)>> = const { RefCell::new(None) };
}
/// Install a programmed table for `programmed_hash` on this thread.
pub fn install(table:Table) { PROGRAMMED.with(|p| *p.borrow_mut()=Some((table,BTreeSet::new()))); }
/// Remove the table; returns (programmed addresses, addresses actually read).
pub fn uninstall()->(usize,usize) {
    PROGRAMMED.with(|p| p.borrow_mut().take().map(|(t,hits)|(t.len(),hits.len())).unwrap_or((0,0)))
}
/// The random oracle of the ideal game as the verifier sees it: programmed
/// answers at published addresses, the real hash everywhere else.
pub fn programmed_hash(parts:&[&[u8]])->[u8;32] {
    let address=concat(parts);
    let hit=PROGRAMMED.with(|p| {
        let mut p=p.borrow_mut();
        let (table,hits)=p.as_mut()?;
        let a=*table.get(&address)?;
        hits.insert(address.clone());
        Some(a)
    });
    hit.unwrap_or_else(|| HOST_HASH(parts))
}

// ------------------------------------------------------- transcript walk
struct Records {
    c1_root:[u8;32],
    semantic:Vec<Vec<u8>>, // 27 framed records
    y1:Vec<u8>, inactive:[u8;32], c0:Vec<u8>, folded_root:[u8;32], c1:Vec<u8>, fin:Vec<u8>,
}
impl Records {
    fn placeholder()->Result<Self,Error> {
        let semantic=(0..27u8).map(|row|wire::record(row,&vec![0;wire::row_shape(row).unwrap().1]).map_err(|_|Error::Semantic)).collect::<Result<Vec<_>,_>>()?;
        Ok(Self{c1_root:[0;32],semantic,y1:vec![0;29*32],inactive:[0;32],c0:vec![0;7*32],folded_root:[0;32],c1:vec![0;7*32],fin:vec![0;64*32]})
    }
}
#[derive(Clone,PartialEq)]
struct Drawn { sem:[K;25], z:[SecureCirclePoint;2], gamma:E, kappa:E, alpha0:E, alpha1:E, queries:[u32;22], rho:K }

/// The prover's transcript order (host_semantic rows 0..26, then the opening
/// rows 27..32 of prove_from_semantics): 115 reads.
fn walk<H:Digest32>(hash:H,public_bytes:&[u8],r:&Records,variant:Variant)->Result<Drawn,Error> {
    let mut st=SemanticTranscript::new(hash,public_bytes,&r.c1_root).map_err(|_|Error::Semantic)?;
    let mut sem=[K::ZERO;25];
    for row in 0..25u8 { sem[row as usize]=st.semantic(row,&r.semantic[row as usize]).map_err(|_|Error::Semantic)?; }
    let z0=st.challenge_reference_circle_point(25,&r.semantic[25]).map_err(|_|Error::Semantic)?;
    let z1=st.challenge_reference_circle_point(26,&r.semantic[26]).map_err(|_|Error::Semantic)?;
    let mut t=Transcript::new(hash,st.state(),variant);
    let gamma=t.scalar(27,&r.y1,true);
    let kappa=t.scalar(28,&r.inactive,false);
    let alpha0=t.scalar(29,&r.c0,false);
    let mut payload=r.folded_root.to_vec();payload.extend_from_slice(&r.c1);
    let alpha1=t.scalar(30,&payload,false);
    let queries=t.queries(31,&r.fin)?;
    let rho=t.scalar_k(32,&[]);
    Ok(Drawn{sem,z:[z0,z1],gamma,kappa,alpha0,alpha1,queries,rho})
}

// ------------------------------------------------------------ the tape τ
struct Tape { c1:[Vec<M31>;26], h1:Vec<K>, g:Vec<K>, d:Vec<K> }

/// The pure-tape trace: the prover's mask material (same derivation, fresh
/// entropy from the coins) applied to the zero C1 trace; H1 is the padding
/// alone (no copy helper is built).
fn tape(public_bytes:&[u8],variant:Variant,coins:&mut Coins)->Result<Tape,Error> {
    let hash=HOST_HASH;
    let nonce=coins.nonzero();
    let context=StateOnlyHidingContext::pool_v1_pair_forest_v1(hash(&[public_bytes]),nonce);
    let binding=hash(&[b"UNPROVED:R1:P3:PRIVATE-ATTEMPT",public_bytes,&[variant.tag()],&context.encode()]);
    let secrets=StateOnlyAttemptSecrets::deterministic_spend_fixture(nonce,coins.nonzero(),coins.nonzero());
    let mut store=InMemoryStateOnlyMaskNonceStore::default();
    let (reserved,material)=secrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash,binding,context,&mut store).map_err(|_|Error::Semantic)?;
    let mut zero=StateOnlyTraceFoundation{c1:core::array::from_fn(|_|vec![M31::ZERO;1024])};
    let applied=apply_pool_v1_pair_forest_mask_material_v1(&mut zero,material).map_err(|_|Error::Semantic)?;
    let d=reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,context).map_err(|_|Error::Semantic)?;
    let mut h1=vec![K::ZERO;1024];
    apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h1,&applied.h1_padding).map_err(|_|Error::Semantic)?;
    if zero.c1.len()!=16||d.len()!=1024||applied.g.len()!=1024
        || crate::prover_helper_sum::state_only_copy_helper_sum(&h1)!=Some(K::ZERO) {return Err(Error::Semantic);}
    let c1=core::array::from_fn(|i| if i<16 {zero.c1[i].clone()} else {applied.mask_only_c1[i-16].clone()});
    Ok(Tape{c1,h1,g:applied.g.clone(),d})
}

// ------------------------------------------------- domain evaluation helpers
fn tcheb(x:M31)->M31 { x.mul(x).double().sub(M31::ONE) }
/// EncodingDomain levels[d][j >> d] for d = 0..8: the only nodes that the
/// evaluation of index j at depth 0 reads (levels[d][i] = T^(d+1)(x_(i·2^d))).
fn nodes_for(j:usize)->[M31;9] {
    core::array::from_fn(|depth|{
        let p=domain::fibre_point::<M31>(FibreIndex::new((j>>depth)<<depth).unwrap());
        let mut n=tcheb(p.x);
        for _ in 0..depth {n=tcheb(n);}
        n
    })
}
fn eval_rec<T:CodeField>(coefficients:&[T],depth:usize,nodes:&[M31;9])->T {
    if coefficients.len()==1 {return coefficients[0];}
    let even:Vec<T>=coefficients.iter().step_by(2).copied().collect();
    let odd:Vec<T>=coefficients.iter().skip(1).step_by(2).copied().collect();
    eval_rec(&even,depth+1,nodes).add(T::from_m31(nodes[depth]).mul(eval_rec(&odd,depth+1,nodes)))
}
/// EncodingDomain::evaluate(coefficients, 0)[j] at one index (≤ 256 coefficients).
pub(crate) fn eval_at<T:CodeField>(coefficients:&[T],j:usize)->T { eval_rec(coefficients,0,&nodes_for(j)) }
/// EncodingDomain::encode(coefficients)[4u..4u+4] at one fibre.
pub(crate) fn encode_at<T:CodeField>(coefficients:&[T;1024],u:usize)->[T;4] {
    let z=domain::fibre_point::<M31>(FibreIndex::new(u).unwrap());
    let nodes=nodes_for(u);
    let channels=core::array::from_fn(|s|{
        let c:Vec<T>=(0..256).map(|d|coefficients[4*d+s]).collect();
        eval_rec(&c,0,&nodes)
    });
    phi_inverse(T::from_m31(z.x),T::from_m31(z.y),channels)
}

// ------------------------------------------------------------ the view
struct View5 { semantic:Vec<Vec<u8>>, y1:Vec<u8>, inactive:[u8;32], c0:Vec<u8>, c1:Vec<u8>, fin:Vec<u8>, q1:Vec<E>, messages:Vec<Message<E>> }

fn challenges_of(d:&Drawn)->Challenges {
    Challenges{lambda:d.sem[0],chi:d.sem[1],theta:d.sem[2],zc:core::array::from_fn(|i|d.sem[3+i]),mu:d.sem[13],eta:d.sem[14]}
}

/// Step 5, semantic part: Ψ_ch(refPayload + L τ) on the semantic cells.
///   mask-sum cell   Σ_b maskLinear(τ)(b) + S₀,  S₀ = Σ_b η·terminal(0)(b)
///   round cells     rounds(maskLinear(τ) + η·terminal(0))  [L τ + originalRounds(0)]
///                   + (originalOf − η·terminal(0)(α))·(α₉−½)⁻¹·(X−½) on round 9
///                   [−k₀·dir from refPayload, then Ψ_ch]
///   claims, extra, OOD cells   those of τ  [L τ; refPayload is 0 there]
fn semantic(public:Public<'_>,tau:&Tape,d:&Drawn,c2_root:&[u8;32],variant:Variant,ablation:Ablation)->Result<(Vec<Vec<u8>>,[Vec<K>;29]),Error> {
    let ch=challenges_of(d);
    let alpha:[K;10]=core::array::from_fn(|i|d.sem[15+i]);
    let lift=|x:M31|K::from_cm31(CM31::from_m31(x));
    let columns:[Vec<K>;29]=core::array::from_fn(|lane| match lane {
        0..=25=>tau.c1[lane].iter().copied().map(lift).collect(),
        26=>tau.h1.clone(),27=>tau.g.clone(),_=>tau.d.clone(),
    });
    let d28:&[K;1024]=columns[28].as_slice().try_into().unwrap();
    let dc=variant.coefficients(d28);
    let zero=[[K::ZERO;29];3];
    let term0=|p:&[K;10]|crate::host_public::terminal_qm31(public,&zero,p,&ch).map_err(|_|Error::Semantic);
    let bits=|row:usize|->[K;10] {core::array::from_fn(|i| if (row>>(9-i))&1==0 {K::ZERO} else {K::ONE})};
    // Mask sum of τ (host_semantic's formula) and S₀.
    let mut mask_sum=K::ZERO;let mut s0=K::ZERO;
    for row in 0..1024 {
        let point=bits(row);
        mask_sum=mask_sum.add(state_only_selected_mask_value(&core::array::from_fn(|i|columns[i][row]),&core::array::from_fn(|i|columns[16+i][row]),columns[27][row],&point));
        s0=s0.add(ch.eta.mul(term0(&point)?));
    }
    for side in 0..2 {
        let h=&dc[28*side..28*(side+1)];
        mask_sum=mask_sum.add(h.iter().copied().fold(h[0],K::add).mul_m31(M31(512)));
    }
    let mask_cell=if ablation==Ablation::NoS0 {mask_sum} else {mask_sum.add(s0)};
    // The point function maskLinear(τ) + η·terminal(0).
    let f=|p:&[K;10]|->Result<K,Error> {
        let at=wire::statement_points(p)[0];
        let ev=|l:usize|multilinear_evaluate_qm31(&columns[l],&at).ok_or(Error::Semantic);
        let mut c1=[K::ZERO;16];for (i,c) in c1.iter_mut().enumerate() {*c=ev(i)?;}
        let mut mo=[K::ZERO;10];for (i,c) in mo.iter_mut().enumerate() {*c=ev(16+i)?;}
        let mask=state_only_selected_mask_value(&c1,&mo,ev(27)?,p);
        Ok(mask.add(extra(&dc,p[8],p[9])).add(ch.eta.mul(term0(p)?)))
    };
    // rounds(·): host_sumcheck's interpolation of the partial Boolean sums.
    let mut polys=[[K::ZERO;28];10];
    let mut point=[K::ZERO;10];let mut running=mask_cell;
    for r in 0..10 {
        let remaining=9-r;let mut values=[K::ZERO;28];
        for (sample,value) in values.iter_mut().enumerate() {
            point[r]=K::from_cm31(CM31::from_m31(M31(sample as u32)));
            for assignment in 0..1usize<<remaining {
                for offset in 0..remaining {
                    point[r+1+offset]=if (assignment>>(remaining-1-offset))&1==0 {K::ZERO} else {K::ONE};
                }
                *value=value.add(f(&point)?);
            }
        }
        polys[r]=crate::host_sumcheck::interpolate(&values);
        if ablation!=Ablation::NoS0 && state_only_boundary_sum(&polys[r])!=running {return Err(Error::Semantic);}
        point[r]=alpha[r];
        running=evaluate_state_only_polynomial(&polys[r],alpha[r]);
    }
    // Claims, extras, the shift on round 9.
    let claims=point_claims(&columns,&alpha).map_err(|_|Error::Semantic)?;
    let extras:[K;29]=core::array::from_fn(|l|extra(&variant.coefficients(columns[l].as_slice().try_into().unwrap()),alpha[8],alpha[9]));
    let original=ch.eta.mul(crate::host_public::terminal_qm31(public,&claims,&alpha,&ch).map_err(|_|Error::Semantic)?);
    let half=K::from_cm31(CM31::from_m31(M31(2).inv()));
    let inv=alpha[9].sub(half).try_inv().ok_or(Error::Semantic)?;
    if ablation!=Ablation::NoShift {
        let c=original.sub(ch.eta.mul(term0(&alpha)?)).mul(inv);
        polys[9][0]=polys[9][0].sub(c.mul(half));
        polys[9][1]=polys[9][1].add(c);
    }
    if ablation==Ablation::None {
        // The verifier's terminal test, by construction.
        let mask=state_only_selected_mask_value(&core::array::from_fn(|i|claims[0][i]),&core::array::from_fn(|i|claims[0][16+i]),claims[0][27],&alpha);
        if evaluate_state_only_polynomial(&polys[9],alpha[9])!=mask.add(original).add(extras[28]) {return Err(Error::Semantic);}
    }
    // Records 0..26.
    let rec=|row:u8,payload:&[u8]|wire::record(row,payload).map_err(|_|Error::Semantic);
    let mut out=Vec::with_capacity(27);
    for row in 0..15u8 {
        out.push(match row {2=>rec(2,c2_root)?,14=>rec(14,&E::from_qm31(mask_cell).to_le_bytes())?,_=>rec(row,&[])?});
    }
    for (r,p) in polys.iter().enumerate() { out.push(rec(15+r as u8,&wire::encode_values(p.map(E::from_qm31)))?); }
    out.push(rec(25,&wire::encode_values(claims.into_iter().flatten().chain(extras).map(E::from_qm31)))?);
    let z0=d.z[0];
    let endpoint=columns.iter().map(|col|{
        let m:&[K;1024]=col.as_slice().try_into().unwrap();
        E::from_qm31(eval_message(&variant.coefficients(m),Point{x:z0.x,y:z0.y}))
    });
    out.push(rec(26,&wire::encode_values(endpoint))?);
    Ok((out,columns))
}

/// Step 5, opening part: the linear cells of τ (prove_from_semantics' formulas).
fn opening(columns:&[Vec<K>;29],tau:&Tape,d:&Drawn,variant:Variant)->Result<View5,Error> {
    let messages:Vec<Message<E>>=(0..29).map(|l| if l<26 {core::array::from_fn(|r|E::from_m31(tau.c1[l][r]))} else {core::array::from_fn(|r|E::from_qm31(columns[l][r]))}).collect();
    let coefficients:Vec<Message<E>>=messages.iter().map(|m|variant.coefficients(m)).collect();
    let z1=Point{x:E::from_qm31(d.z[1].x),y:E::from_qm31(d.z[1].y)};
    let y1=encoded(coefficients.iter().map(|m|eval_message(m,z1)));
    let gp=crate::prover_powers::powers::<29>(d.gamma);
    let q:Vec<E>=(0..1024).map(|j|(0..29).fold(E::ZERO,|s,l|s.add(gp[l].mul(coefficients[l][j])))).collect();
    let alpha:[K;10]=core::array::from_fn(|i|d.sem[15+i]);
    let w=Weights::new(variant,&alpha,&d.z)?;
    let inactive=(0..1024).fold(E::ZERO,|s,j|s.add(q[j].mul_qm31(w.raw(0,j))));
    let mut weights=match aspis_core::r0::heap::filled(1024,E::ZERO) { Ok(v)=>v, Err(_)=>return Err(Error::Allocation) };
    w.materialize(d.kappa,weights.as_mut_slice().try_into().unwrap())?;
    let c0=encoded(round(&q,&weights));
    let q1=fold(&q,d.alpha0,false);let w1=fold(&weights,d.alpha0,true);
    let c1=encoded(round(&q1,&w1));
    let fin=encoded(fold(&q1,d.alpha1,false).into_iter());
    Ok(View5{semantic:vec![],y1,inactive:inactive.to_le_bytes(),c0,c1,fin,q1,messages})
}

// ------------------------------------------------- commitment programming
/// Sparse binary tree containing exactly the opened path union. Sibling
/// digests are coins, stored for multiproof assembly without oracle reads.
struct ProgrammedTree { children: Vec<BTreeMap<usize, [[u8;32];2]>> }
impl ProgrammedTree {
    fn multiproof(&self, indices:&[u32])->Result<Vec<u8>,Error> {
        multiproof::generate(multiproof::Arity::Two,indices,|depth,index| {
            self.children[depth as usize][&(index as usize/2)][index as usize%2]
        }).ok_or(Error::Merkle)
    }
}

/// Program leaves and each distinct binary parent in the union of both
/// transaction batches. Shared nodes receive one consistent answer, including
/// the root coin. Each batch later emits its own canonical sibling sequence.
fn program_tree(table:&RefCell<(Table,bool)>,coins:&mut Coins,tag:u8,leaves:&BTreeMap<usize,(Vec<u8>,[u8;32])>,root:[u8;32])->Result<(ProgrammedTree,usize),Error> {
    let mut reads=0;
    let mut level=BTreeMap::new();
    for (&i,(value,salt)) in leaves {
        let answer=coins.coin();
        private_leaf_hash_with_digest(ProgramOne{table,answer},tag,value,salt);
        level.insert(i,answer);reads+=1;
    }
    let mut children=Vec::new();
    for depth in 0..multiproof::LEAF_BITS {
        let parents:BTreeSet<usize>=level.keys().map(|i|i/2).collect();
        let (mut next,mut kids_here)=(BTreeMap::new(),BTreeMap::new());
        for p in parents {
            let kids=core::array::from_fn(|s|level.get(&(2*p+s)).copied().unwrap_or_else(||coins.coin()));
            let answer=if depth+1==multiproof::LEAF_BITS {root} else {coins.coin()};
            multiproof::binary_parent(ProgramOne{table,answer},&kids[0],&kids[1]);reads+=1;
            next.insert(p,answer);kids_here.insert(p,kids);
        }
        children.push(kids_here);level=next;
    }
    if level.len()!=1||level.get(&0)!=Some(&root) {return Err(Error::Merkle);}
    Ok((ProgrammedTree{children},reads))
}

// ------------------------------------------------------------- simE
pub fn sim_e(public:Public<'_>,seed:[u8;32])->Result<Simulated,Error> { sim_e_ablated(public,seed,Ablation::None) }

#[doc(hidden)]
pub fn sim_e_ablated(public:Public<'_>,seed:[u8;32],ablation:Ablation)->Result<Simulated,Error> {
    let variant=Variant::S2;
    let start=std::time::Instant::now();
    let mut times=SimTimes::default();
    let public_bytes=crate::host_public::materialize_public_bytes(public).map_err(|_|Error::Semantic)?;
    for k in 0..ATTEMPT_CAP {
        // 1–2. Coins and the draw.
        let t=std::time::Instant::now();
        let mut transcript_coins=Coins::new(seed,k as u32,0);
        let mut root_coins=Coins::new(seed,k as u32,1);
        let mut commit_coins=Coins::new(seed,k as u32,2);
        let mut tape_coins=Coins::new(seed,k as u32,3);
        let answers:Vec<[u8;32]>=(0..115).map(|_|transcript_coins.coin()).collect();
        let roots=[root_coins.coin(),root_coins.coin(),root_coins.coin()];
        let state=RefCell::new(CoinState{coins:answers,next:0,record:None,collision:false});
        let drawn=walk(CoinOracle(&state),&public_bytes,&Records::placeholder()?,variant);
        times.draw+=t.elapsed().as_secs_f64();
        let drawn=match drawn {Ok(d) if state.borrow().next==115 && d.z[0]!=d.z[1]=>d,_=>continue};
        // 3. P_R1 on the drawn challenges.
        let t=std::time::Instant::now();
        let check=R1PublicChallenges{alpha:core::array::from_fn(|i|drawn.sem[15+i]),z:[[drawn.z[0].x,drawn.z[0].y],[drawn.z[1].x,drawn.z[1].y]],
            gamma:drawn.gamma,kappa:drawn.kappa,alpha0:drawn.alpha0,alpha1:drawn.alpha1,queries:drawn.queries.to_vec()};
        let (accepted,_)=aspis_z4b_probe::p_r1_check(&check);
        times.p_r1+=t.elapsed().as_secs_f64();
        if !accepted {continue;}
        // 4. The tape.
        let t=std::time::Instant::now();
        let tau=tape(&public_bytes,variant,&mut tape_coins)?;
        times.tape=t.elapsed().as_secs_f64();
        // 5. The view.
        let t=std::time::Instant::now();
        let (semantic_records,columns)=semantic(public,&tau,&drawn,&roots[1],variant,ablation)?;
        times.semantic=t.elapsed().as_secs_f64();
        let t=std::time::Instant::now();
        let mut view=opening(&columns,&tau,&drawn,variant)?;
        view.semantic=semantic_records;
        times.opening=t.elapsed().as_secs_f64();
        // 6. Commitment programming and serialisation.
        let t=std::time::Instant::now();
        let table=RefCell::new((Table::new(),false));
        let coeffs:Vec<Message<E>>=view.messages.iter().map(|m|variant.coefficients(m)).collect();
        let base:Vec<[M31;1024]>=(0..26).map(|l|coeffs[l].map(|x|M31(x.to_limbs()[0]))).collect();
        let ext:Vec<[K;1024]>=(26..29).map(|l|coeffs[l].map(|x|x.c0())).collect();
        let mut opened:BTreeMap<usize,([[E;29];4],Vec<u8>,Vec<u8>)>=BTreeMap::new();
        for &u in &drawn.queries {
            let u=u as usize;
            let mut values=[[E::ZERO;29];4];
            for l in 0..26 { let v=encode_at(&base[l],u); for s in 0..4 {values[s][l]=E::from_m31(v[s]);} }
            for l in 26..29 { let v=encode_at(&ext[l-26],u); for s in 0..4 {values[s][l]=E::from_qm31(v[s]);} }
            let mut c1v=Vec::with_capacity(480);let mut c2v=Vec::with_capacity(128);
            for s in 0..4 { for l in (0..26).chain(core::iter::once(28)) {c1v.extend_from_slice(&values[s][l].to_le_bytes()[..if l<26 {4} else {16}]);} }
            for s in 0..4 { for l in 26..28 {c2v.extend_from_slice(&values[s][l].to_le_bytes()[..16]);} }
            opened.insert(u,(values,c1v,c2v));
        }
        let mut folded:BTreeMap<usize,Vec<u8>>=BTreeMap::new();
        for &u in &drawn.queries { let v=u as usize/4; folded.entry(v).or_insert_with(||encoded((4*v..4*v+4).map(|i|eval_at(&view.q1,i)))); }
        let mut leaves1=BTreeMap::new();let mut leaves2=BTreeMap::new();let mut leavesf=BTreeMap::new();
        for (&u,(_,c1v,c2v)) in &opened { leaves1.insert(u,(c1v.clone(),commit_coins.coin())); leaves2.insert(u,(c2v.clone(),commit_coins.coin())); }
        for (&v,fv) in &folded { leavesf.insert(v,(fv.clone(),commit_coins.coin())); }
        let (p1,r1)=program_tree(&table,&mut commit_coins,merkle::C1_TAG,&leaves1,roots[0])?;
        let (p2,r2)=program_tree(&table,&mut commit_coins,merkle::C2_TAG,&leaves2,roots[1])?;
        let (pf,rf)=program_tree(&table,&mut commit_coins,0x72,&leavesf,roots[2])?;
        let records=Records{c1_root:roots[0],semantic:view.semantic.clone(),y1:view.y1.clone(),inactive:view.inactive,c0:view.c0.clone(),folded_root:roots[2],c1:view.c1.clone(),fin:view.fin.clone()};
        let mut out=Vec::with_capacity(compact::PROOF_BYTES);
        out.extend_from_slice(compact::MAGIC);out.extend_from_slice(&[variant.tag(),0,0,0,0,0,0,0]);
        let mut logical=records.c1_root.to_vec();
        for r in &records.semantic {logical.extend_from_slice(r);}
        compact::compact_semantic(&logical,&mut out).map_err(|_|Error::Semantic)?;
        compact::compact_values(&records.y1,&mut out).map_err(|_|Error::Semantic)?;
        out.extend_from_slice(&records.inactive);out.extend_from_slice(&records.c0);
        out.extend_from_slice(&records.folded_root);out.extend_from_slice(&records.c1);out.extend_from_slice(&records.fin);
        for &u in &drawn.queries {
            let u=u as usize;let (_,c1v,c2v)=&opened[&u];
            out.extend_from_slice(c1v);out.extend_from_slice(c2v);
            out.extend_from_slice(&leaves1[&u].1);out.extend_from_slice(&leaves2[&u].1);
            out.extend_from_slice(&folded[&(u/4)]);out.extend_from_slice(&leavesf[&(u/4)].1);
        }
        if out.len()!=compact::OFF_NODES {return Err(Error::Parse);}
        for (batch,range) in [(0,0..compact::SPLIT),(1,compact::SPLIT..compact::QUERIES)] {
            for (tree,programmed) in [&p1,&p2,&pf].into_iter().enumerate() {
                let mut indices:Vec<u32>=drawn.queries[range.clone()].iter().map(|&u|if tree==2 {u/4} else {u}).collect();
                indices.sort();indices.dedup();
                let nodes=programmed.multiproof(&indices)?;
                let cap=32*compact::SLOT_NODES[3*batch+tree];
                if nodes.len()>cap {return Err(Error::Parse);}
                out.extend_from_slice(&nodes);out.resize(out.len()+cap-nodes.len(),0);
            }
        }
        if out.len()!=compact::PROOF_BYTES {return Err(Error::Parse);}
        // VerLog, transcript part: the same answers at the view's addresses.
        let state=RefCell::new(CoinState{coins:state.into_inner().coins,next:0,record:Some(Table::new()),collision:false});
        let again=walk(CoinOracle(&state),&public_bytes,&records,variant)?;
        let state=state.into_inner();
        if again!=drawn||state.next!=115||state.collision {return Err(Error::Transcript);}
        let (mut table,collision)=table.into_inner();
        if collision {return Err(Error::Merkle);}
        let transcript=state.record.unwrap();
        let transcript_reads=transcript.len();
        for (a,v) in transcript { if let Some(p)=table.insert(a,v) { if p!=v {return Err(Error::Transcript);} } }
        times.program=t.elapsed().as_secs_f64();
        times.total=start.elapsed().as_secs_f64();
        return Ok(Simulated{proof:out,table,attempts:k+1,transcript_reads,commitment_reads:r1+r2+rf,times});
    }
    Err(Error::AttemptsExhausted)
}

/// Verify a simulated proof under its programmed oracle (strict tx1 + tx2,
/// then the dense verifier). Returns (accepted, programmed, read).
/// Both verifiers parse the adopted compact binary-multiproof format.
pub fn verify_programmed(public:Public<'_>,proof:&[u8],table:Table)->(Result<(),Error>,usize,usize) {
    install(table);
    let hash:HashFn=programmed_hash;
    let result=(|| {
        let public_bytes=crate::host_public::materialize_public_bytes(public).map_err(|_|Error::Semantic)?;
        let cp=crate::verifier::tx1(public,&public_bytes,proof,crate::verifier::SPLIT,LegacyHashFn(hash),None)?;
        crate::verifier::tx2(&public_bytes,proof,&cp,LegacyHashFn(hash),None)?;
        crate::dense::verify(public,proof,hash).map_err(|_|Error::Relation)
    })();
    let (programmed,read)=uninstall();
    (result,programmed,read)
}

#[cfg(test)]
#[path="sim_tests.rs"]
mod tests;

// Proof-only owned references. Not enabled in any production configuration.
#[cfg(any(kani,aeneas_ref))]
pub mod owned19 {
    use alloc::vec::Vec;
    pub fn concat(parts:Vec<Vec<u8>>,index:usize,mut output:Vec<u8>)->Vec<u8> {
        if index==parts.len() { return output; }
        let part=parts[index].clone();
        output.extend_from_slice(&part);
        concat(parts,index.wrapping_add(1),output)
    }
    // One program-table transition, including conflict retention.
    // The table is represented by unique-key entries; ordering is immaterial
    // to lookup, while the simulator's public iteration order needs transport.
    pub fn insert(mut table:Vec<(Vec<u8>,[u8;32])>,index:usize,address:Vec<u8>,answer:[u8;32],collision:bool)
        ->(Vec<(Vec<u8>,[u8;32])>,bool) {
        if index==table.len() {
            table.push((address,answer));
            return (table,collision);
        }
        let (key,previous)=table[index].clone();
        if key==address {
            table[index]=(key,answer);
            (table,collision || previous!=answer)
        } else {
            insert(table,index.wrapping_add(1),address,answer,collision)
        }
    }

    // Owned recursion for the actual walk's 25 semantic transcript rows.
    // The callee is unchanged. Both its advanced transcript and semantic
    // error are retained; no callback success or hash law is asserted here.
    pub fn semantic_rows<H:aspis_core::Digest32>(
        mut state:crate::r1_wire::SemanticTranscript<H>, records:Vec<Vec<u8>>,
        row:usize,mut sem:[aspis_core::field::QM31;25])
        ->Result<(crate::r1_wire::SemanticTranscript<H>,[aspis_core::field::QM31;25]),super::Error> {
        if row==25 {return Ok((state,sem));}
        let record=records[row].clone();
        let value=state.semantic(row as u8,&record).map_err(|_|super::Error::Semantic)?;
        sem[row]=value;
        semantic_rows(state,records,row.wrapping_add(1),sem)
    }
}

// One iteration of the native walk's semantic prefix, with owned inputs.
// The production loop above remains the source of the iteration statement.
// The owned callee is the retained P6 semantic20 reference, not a new sampler.
#[cfg(any(kani,aeneas_ref))]
pub mod owned29 {
    use super::*;
    pub fn semantic_step<H:Digest32>(st:SemanticTranscript<H>, row:u8,
        record:Vec<u8>, mut sem:[K;25])
        ->Result<(SemanticTranscript<H>,[K;25]),Error> {
        let (value,st)=crate::r1_wire::semantic20::semantic(st,row,record);
        match value {
            Err(_)=>Err(Error::Semantic),
            Ok(value)=>{sem[row as usize]=value;Ok((st,sem))}
        }
    }
    // Record selection is part of the native iteration, before the semantic
    // call. Index failure and cloning remain explicit in its extracted owner.
    pub fn iteration<H:Digest32>(st:SemanticTranscript<H>,row:u8,
        records:Vec<Vec<u8>>,sem:[K;25])
        ->Result<(SemanticTranscript<H>,[K;25]),Error> {
        let record=records[row as usize].clone();
        semantic_step(st,row,record,sem)
    }

}

#[cfg(any(kani,aeneas_ref))]
#[path="sim_owned31.rs"]
pub mod owned31;

#[cfg(any(kani,aeneas_ref))]
#[path="sim_owned32.rs"]
pub mod owned32;
