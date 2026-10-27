# XRb declaration comparison and eight-cut status

**Full release association is blocked, not proved.** The exact release translation failed before writing Types/Funs. No honest declaration-level diff against *complete fresh release Types/Funs*, no class-(b) release equality proof, and no complete a/b/c partition can be delivered from this run. The two successful diagnostic derivatives are deliberately not relabeled as the requested extraction. No XRb_Association.lean is manufactured from an unextracted body or an assumed equality.

## Inputs and scope

Selected cohort sources are exactly L8a's coherent resolution: union Types b45ee7357278642101b81933252e81f5068c937487acfdebb4f82f991c91bb83 and Prepared-only adapted Funs 544b75b962ade326ff1069b6986805a175cc90db1c592b1c524dffcd94693d2d. Their repository paths and sizes are in XRb_declaration_diff.json. No alternate producer/source is substituted.

Historical raw e5c Types bb4ccfd7a77b6e45de16181113c888febda2ecf8c23bdad55c1919fe92762c3e / Funs f4aee2661033aeaf820623a7decb3687e2617ae50a2ad4b41e78b253025a1de1 are extracted read-only from the retained tx1 archive. Both quoted raw source files are retained as .lean.txt; they are not new imported modules.

Diagnostic XRb_004/005 Types eb031a5234fdf0e3b8335eeb7b635d303af8155e094e69b8abb52c1eab89d67d preserves decoded type declarations. XRb_005 Funs 4b6fddc7d04c62fdd05daedfdf771d51a2b4a24a0212d8f3163f53b7c362f0e6 retains ONLY original Fun0 tx1 and Fun44 Prepared.new structured bodies; other structured bodies are made Opaque. TypesExternal and FunsExternal templates are NOT implementations. No generated axiom, placeholder, sorry or external template is promoted to a proof. All masking and input hashes are explicit in XRb_004_mask.json / XRb_005_mask.json.

XRb_compare.py emits the complete per-declaration inventory and normalized text differences in XRb_declaration_diff.json and six .diff files. Normalization removes comments/attributes/whitespace and compares SAME declaration names only. Counts are text observations, not Lean equalities or a proof of carrier/namespace transport. Rust namespace association also differs: the kit inlined aspis_core/pool_v1; release uses actual dependency crates.

| Comparison | Left only | Right only | Same normalized | Different normalized |
|---|---:|---:|---:|---:|
| historical Types → cohort Types | 0 | 19 | 25 | 1 |
| historical Funs → cohort Funs | 15 | 66 | 16 | 5 |
| diagnostic Types → cohort Types | 20 | 29 | 11 | 5 |
| diagnostic Funs → cohort Funs | 17 | 87 | 0 | 0 |
| diagnostic Types → historical Types | 20 | 10 | 11 | 5 |
| diagnostic Funs → historical Funs | 15 | 34 | 1 | 1 |

The selected Funs has no verifier.tx1 or verifier.Prepared.new body. Those are present in raw historical Funs, and in the diagnostic release Funs under the actual release names. The producer cohort therefore cannot be certified merely by renaming those two files. External/bridge owners and their carriers must be identified and proved as part of any later association. No absence of a declaration is itself claimed to refute the enclosing top theorem.

## Eight cuts

A class-(b) assignment means an actual proved equality of extracted definitions, not a plausible Rust refactoring. Consequently pending rows below are deliberately unclassified. The requested trichotomy has not been completed. Genuine carrier/interface differences (c) are distinguished from an attack, a successful-input counterexample, and an inequality theorem about a proposed transport; none of those stronger claims was proved.

| Cut | Established status | Exact reason / missing equality |
|---|---|---|
| verify_observed | Pending; opaque child in both extractions | Historical loop is refactored into semantic_rounds / verify_finish. Exact release LLBC Fun43 is Opaque. The selector intentionally extracts no body here. Need a SAME-carrier source association; neither identity nor refactoring equality is proved. |
| verifier_error | (a), identical constructor definition at selected features | The three added Rust variants are cfg(prover), disabled here. The actual release type contains exactly Parse, Semantic, Transcript, Relation, Merkle, Query, Checkpoint, Allocation in the historical order. Normalized verifier.Error declaration matches raw and cohort; only diagnostic generation was completed. No cfg(prover) result is inferred. |
| dot_type | (c), genuine carrier/API difference | Historical canonical::Dot has sums and count; release has sums only. The private push count check is removed; public enclosing accumulators retain their checks. Dot itself is not in the raw historical emitted Types (opaque fast_pairing boundary), so no equality of its absent extracted definitions can be claimed. A reachability/bound invariant and representation transport would be needed for an enclosing equivalence. |
| prepared_new | Pending; scratch-output refactoring not proved equal | Historical new returns Prepared; release additionally threads &mut [E;29], producing a backward scratch result. The exact typed equality must include scratch output/error behavior and the concrete prepared_claim/powers association; projecting Prepared alone and asserting equality would omit this obligation. Diagnostic Fun44 translates, but no certified whole-program equality follows. |
| prepared_claim | (c), different extracted child interface | Historical opaque declaration consumes gamma:WideExact; release Fun240 consumes g:&[WideExact;29]. An equality must relate g to the successful result of powers 29 gamma, bind both error paths and the concrete child implementation. Arbitrary inputs to these two interfaces are not interchangeable. No inequality of a properly restricted transport is asserted. |
| query_geometry | (c), genuine carrier difference | Historical record contains start,inverses; release adds line_z:Vec<M31>. Need an invariant tying the cache to query rows, including errors and usage; dropping the field does not prove the operations equivalent. |
| tx1 | (c), distinct root and execution interface | Historical verifier.tx1 accepts k≤22 before its View.parse and dispatches the retired eight-way path; release candidate.tx1 requires k=SPLIT and the compact parser, expansion, batched binary multiproofs and deferred weights. Its checkpoint binds compact stored bytes. This is a changed source-to-protocol mapping, not a naming-only change. No acceptance/non-vacuity or attack claim is inferred from this comparison. |
| tx1_finish | (c), historical declaration absent in release closure | Retired helper performs query_with_geometry and checkpoint; adopted path uses candidate.query_loop plus BatchedWeights.finish and checkpoint in candidate.tx1. There is no release tx1_finish definition to equate. A statement relating the complete continuations, physical proof carrier and ordered effects is required. |

Class-(b) equalities proved: **none**. Candidate equations such as `oldNew ... = map projectPrepared (newNew ... scratch)` are NOT stated as Lean theorems: old/new carriers, dictionaries and scratch/error transport have not been jointly defined, and the exact release extraction failed. A claimed exact Lean equality at this point would be ill-typed or rely on unproved interpretation assumptions. Per common rule4, stop that item rather than insert a desired equality as a hypothesis.

## Exact source quotes

Each historical quote is the byte-pinned raw source cut in XRa_historical_source-pins.json; each release quote is read using git show 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Standalone quote files preserve bytes. LLBC metadata (XRb_release_declarations.json) independently records reached release names, spans, signatures and opacity.

### verify_observed

Historical:

```rust
#[inline(never)]
pub fn verify_observed<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H, obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {
    fn mark(obs: crate::verifier::Observer, i: u8) {
        #[cfg(feature="detail-phases")]
        if let Some(f)=obs {f(crate::verifier::Phase::SemanticPart(i));}
        #[cfg(not(feature="detail-phases"))]
        let _=(obs,i);
    }
    let prefix = Prefix::parse(bytes)?;
    mark(obs, 0);
    let mut transcript = public_transcript(public, hash, prefix.c1_root)?;
    let challenges = wire::begin(&prefix, &mut transcript)?;
    mark(obs, 1);
    let mut running = prefix.validated_record(14)?.decode_k::<1>(0)?[0];
    let mut alpha = [QM31::ZERO; 10];
    #[cfg(feature = "prover")]
    let mut round_checks = [[QM31::ZERO; 3]; 10];
    for round in 0..10 {
        let row = 15 + round as u8;
        let polynomial = prefix.validated_record(row)?.decode_k::<28>(0)?;
        let boundary = polynomial.iter().copied().fold(polynomial[0], QM31::add);
        if boundary != running {
            return Err(Error::Boundary { round });
        }
        alpha[round] = transcript.semantic_validated(prefix.validated_record(row)?)?;
        let value = polynomial
            .iter()
            .rev()
            .fold(QM31::ZERO, |a, &c| a.mul(alpha[round]).add(c));
        #[cfg(feature = "prover")]
        {
            round_checks[round] = [running, boundary, value];
        }
        running = value;
    }
    mark(obs, 2);
    let claims = claims(&prefix)?;
    let original_challenges = aspis_core::state_only_prefix::r0::Challenges {
        lambda: challenges.lambda,
        chi: challenges.chi,
        theta: challenges.theta,
        zc: challenges.zc,
        mu: challenges.mu,
        eta: challenges.eta,
    };
    let terminal = public
        .terminal_qm31(&claims, &alpha, &original_challenges)
        .map_err(|_| Error::Public)?;
    mark(obs, 3);
    let mask = aspis_core::state_only_hiding::state_only_selected_mask_value(
        &core::array::from_fn(|i| claims[0][i]),
        &core::array::from_fn(|i| claims[0][16 + i]),
        claims[0][27],
        &alpha,
    );
    let extra = prefix.validated_record(25)?.decode_k::<29>(87)?;
    let masked_terminal = mask.add(challenges.eta.mul(terminal)).add(extra[28]);
    if running != masked_terminal {
        return Err(Error::Terminal);
    }
    mark(obs, 4);
    let state_before_z0 = transcript.state();
    let z0 = transcript.circle_validated(prefix.validated_record(25)?)?;
    let before_z1 = prefix.validated_record(26)?.decode_k::<29>(0)?;
    let z1 = transcript.circle_validated(prefix.validated_record(26)?)?;
    mark(obs, 5);
    #[cfg(feature = "prover")]
    {
        for (i, x) in [z0.x, z0.y, z1.x, z1.y].into_iter().enumerate() {
            crate::trace::value(3, i, aspis_core::field::WideExact::from_qm31(x));
        }
        for (i, x) in challenges.with_alphas(&alpha).into_iter().enumerate() {
            crate::trace::value(0, i, x);
        }
        for (i, row) in round_checks.iter().enumerate() {
            for (j, x) in row.iter().enumerate() {
                crate::trace::value(1, 3 * i + j, aspis_core::field::WideExact::from_qm31(*x));
            }
        }
        crate::trace::value(2, 0, aspis_core::field::WideExact::from_qm31(terminal));
        crate::trace::value(
            2,
            1,
            aspis_core::field::WideExact::from_qm31(masked_terminal),
        );
    }
    if z0 == z1 {
        return Err(Error::EqualCirclePoints);
    }
    Ok(Verified {
        roots: [*prefix.c1_root, prefix.payload(2)?.try_into().unwrap()],
        challenges,
        alpha,
        claims,
        extra,
        before_z1,
        state_before_z0,
        z: [z0, z1],
        transcript,
        #[cfg(feature = "prover")]
        round_checks,
        #[cfg(feature = "prover")]
        terminal,
        #[cfg(feature = "prover")]
        masked_terminal,
    })
}
```

Release:

```rust
pub fn verify_observed<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H, obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {
    let prefix = Prefix::parse(bytes)?;
    mark(obs, 0);
    let mut transcript = public_transcript(public, hash, prefix.c1_root)?;
    let challenges = wire::begin(&prefix, &mut transcript)?;
    mark(obs, 1);
    verify_finish(public, prefix, transcript, challenges, obs)
}
```

### verifier_error

Historical:

```rust
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
```

Release:

```rust
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation,
    /// Host prover only (LOG D38.3): this attempt's challenges fail the public
    /// P_R1 check. Carries no challenge and no conjunct.
    #[cfg(feature="prover")] Rejected,
    /// Host prover only (D38.3): all N = 8 attempts were rejected; nothing is published.
    #[cfg(feature="prover")] AttemptsExhausted,
    /// Host prover only: the operating-system entropy source failed.
    #[cfg(feature="prover")] Entropy }
```

### dot_type

Historical:

```rust
    // Private canonical operands; bounded raw representatives, canonical result.
    // At most 4096 partial folds, each <2^34, sum <2^46. No u64 wrap.
    pub struct Dot { sums:[u64;4], count:usize }
```

Release:

```rust
pub struct Dot { sums:[u64;4] }
```

### prepared_new

Historical:

```rust
    #[inline(never)]
    pub fn new<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<'_>,hash:H)->Result<Box<Self>,Error> {
        let mut t=Transcript::new(hash,sem.transcript.state(),v.variant);
        let gamma=t.scalar(27,v.y1,true);
        let kappa=t.scalar(28,&v.inactive.to_le_bytes(),false);
        let alpha0=t.scalar(29,v.round0,false);
        let (alpha,row)=if v.variant.folds()==2 {
            let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);
            ([alpha0,t.scalar(30,&bytes,false)],31)
        } else {
            ([alpha0,E::ZERO],30)
        };
        let queries=t.queries(row,v.final_message)?;
        let rho=t.scalar_k(row+1,&[]);
        let claim=prepared_claim(sem,v.y1,v.inactive,gamma,kappa)?;
        Ok(Box::new(Self{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}))
    }
```

Release:

```rust
pub fn new<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<'_>,hash:H,g:&mut [E;29])->Result<Box<Self>,Error> {
        let mut t=Transcript::new(hash,sem.transcript.state(),v.variant);
        let gamma=t.scalar(27,v.y1,true);
        let kappa=t.scalar(28,&v.inactive.to_le_bytes(),false);
        let alpha0=t.scalar(29,v.round0,false);
        let (alpha,row)=if v.variant.folds()==2 {
            let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);
            ([alpha0,t.scalar(30,&bytes,false)],31)
        } else {
            ([alpha0,E::ZERO],30)
        };
        let queries=t.queries(row,v.final_message)?;
        let rho=t.scalar_k(row+1,&[]);
        // Reuse this caller-owned scratch array in tx1; it is never serialized.
        *g=powers::<29>(gamma);
        let claim=prepared_claim(sem,v.y1,v.inactive,g,kappa)?;
        Ok(Box::new(Self{variant:v.variant,roots:sem.roots,gamma,kappa,alpha,rho,queries,semantic_alpha:sem.alpha,z:sem.z,claim,state:t.state}))
    }
```

### prepared_claim

Historical:

```rust
fn prepared_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,gamma:E,kappa:E)->Result<E,Error> {
        let g=powers::<29>(gamma);let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        for point in 0..6 {
            let mut dot=crate::fast_pairing::EbyKDot::new();
            for l in 0..29 {
                let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
                dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
            }
            parts[point+1]=dot.finish();
        }
        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        Ok(claim)
}
```

Release:

```rust
fn prepared_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        for point in 0..6 {
            let mut dot=crate::fast_pairing::EbyKDot::new();
            for l in 0..29 {
                let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
                dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
            }
            parts[point+1]=dot.finish();
        }
        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        Ok(claim)
}
```

### query_geometry

Historical:

```rust
/// The five base-field denominators used to fold one sampled query: circle
/// x/y, followed by line x/y/z. Their inverses are batch-computed once per
/// transaction so each query avoids five independent field inversions.
struct QueryGeometry { start:usize, inverses:Vec<[M31;5]> }
```

Release:

```rust
struct QueryGeometry { start:usize, inverses:Vec<[M31;5]>, line_z:Vec<M31> }
```

### tx1

Historical:

```rust
#[inline(never)]
pub fn tx1<H:Digest32>(public:Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
    if k>22 {return Err(Error::Parse);}
    let v=View::parse(proof)?;mark(obs,Phase::Parsed);
    let sem=crate::r1_semantic::verify_observed(public,v.semantic,hash,obs).map_err(|_|Error::Semantic)?;mark(obs,Phase::Semantic);
    let p=Prepared::new(&sem,&v,hash)?;let mut a=Accumulator::new(v.variant)?;let g=powers::<29>(p.gamma);mark(obs,Phase::Prepare);
    tx1_finish(v,p,a,g,public_bytes,proof,k,hash,obs)
}
```

Release:

```rust
pub fn tx1<H: Digest32>(public: Public<'_>, public_bytes: &[u8], proof: &[u8], k: usize, hash: H, obs: Observer) -> Result<Vec<u8>, Error> {
    if k != SPLIT {
        return Err(Error::Parse);
    }
    parse_shape(proof)?;
    canonical_scan(proof)?;
    mark(obs, Phase::Parsed);
    let mut g = [E::ZERO; 29];
    let p = prepare(public, proof, hash, obs, &mut g)?;
    let a = Accumulator::new(Variant::S2)?;
    mark(obs, Phase::Prepare);
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    batch_merkle(proof, &p, &folded_root, 0, hash)?;
    mark(obs, Phase::Merkle(0));
    let geometry = QueryGeometry::for_range(&p.queries, 0, k)?;
    let pending = BatchedWeights::new(&a.weights)?;
    let (mut a, pending) = query_loop(proof, &p, a, &g, obs, &geometry, pending, k)?;
    pending.finish(&mut a.weights);
    let bytes = checkpoint(&p, &a, proof, public_bytes, hash);
    mark(obs, Phase::CheckpointWrite);
    Ok(bytes)
}
```

### tx1_finish

Historical:

```rust
fn tx1_finish<H:Digest32>(v:View<'_>,p:Box<Prepared>,mut a:Accumulator,g:[E;29],public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
    let geometry=QueryGeometry::for_range(&p.queries,0,k)?;
    while a.next<k {query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry)?;}
    let bytes=checkpoint(&p,&a,proof,public_bytes,hash);mark(obs,Phase::CheckpointWrite);Ok(bytes)
}
```

Release continuation component (no tx1_finish definition):

```rust
fn query_loop(proof: &[u8], p: &Prepared, mut a: Accumulator, g: &[E; 29], obs: Observer, geometry: &QueryGeometry, pending: BatchedWeights, end: usize) -> Result<(Accumulator, BatchedWeights), Error> {
    let mut state = Ok((a, pending));
    loop {
        match state {
            Err(error) => return Err(error),
            Ok((a, pending)) => {
                if a.next >= end {
                    return Ok((a, pending));
                }
                state = query_values(proof, p, a, g, obs, geometry, pending);
            }
        }
    }
}
```
