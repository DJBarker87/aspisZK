# R563: frozen R117 initial-claim and eta dependencies

Read-only source inventory. No build, execution, producer, search, or proof run. The inspected frozen NUC tree is `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`, the R117 source freeze at revision `6677d5f1310ff7373301fbd79f186278f772e68a`. The snapshot has no Git metadata; the revision is from the pinned campaign receipt. Exact-source copies used for critical claims are preserved under `frozen-r117/`; all listed bytes were copied from that tree and SHA-256 checked. This note does not decide grinding probability, acceptance, or a privacy/security game.

## Exact selected verifier order

The selected R117 verifier is `docs/research/v8-no-work-100-20260907/experiments/performance_verifier.rs`, SHA-256 `d6dad89eaa8d735f467055e96a8df12de7a391e2475ec26c44b2bc493624a62a` (copied frozen bytes: `frozen-r117/docs/research/v8-no-work-100-20260907/experiments/performance_verifier.rs`). Its `semantic` function, lines 33–60, gives the order:

1. `Transcript::new(hash)`; the selected `df02` flags enable `v8_positive_transfer`, so the positivity profile is absorbed before the remaining base profile.
2. Absorb statement binding and `w.roots.0`; sample `lambda`, then `chi` (lines 34–43).
3. Absorb `w.roots.1`, then call `begin_state_only_zerocheck` to obtain `theta`, ten `zc` values and `mu` (lines 44–45).
4. First use `w.v[0]` in the transcript challenge schedule here: `begin_state_only_masked_sumcheck(&mut t,w.v[0])` absorbs it and samples nonzero `eta` (line 46).
5. The selected `semantic` entry delegates to `semantic_cached(..., &mut [])`, so the selected path takes the empty-cache branch (lines 33–38). For each round it reads 27 sent coefficients, absorbs only round index plus sent bytes, samples the point, then derives omitted `poly[1]` from the current claim and evaluates the polynomial (lines 48–60). It derives the omitted coefficient; it does **not** run the producer's generic explicit boundary-mismatch check.
6. It evaluates the selected terminal using the final point/claims and rejects with `Error::Terminal` on inequality (lines 89–93).

Consequently, at the point just before `w.v[0]` is absorbed, `lambda`, `chi`, `theta`, `zc`, and `mu`, as well as both already supplied commitment roots, are determined without `w.v[0]`. Changing only `w.v[0]` changes the state used to sample `eta` and all later challenge derivation. Even with the same transmitted semantic-round bytes, the first and later round challenges are drawn from the changed transcript state. The verifier derives the omitted coefficient from the new running claim, rather than checking a producer-style boundary condition. This is only a transcript-dependency fact; no claim is made that such a mutated wire is accepted.

`begin_state_only_zerocheck` is frozen `crates/aspis-core/src/state_only_sumcheck.rs`, SHA-256 `5458d3134a3123b8b02bef0374ccbf96a05461974d7e274966c6a3f0d2d496f9`, copied under `frozen-r117/crates/aspis-core/src/`. Lines 80–106 absorb the fixed registry/helper-sum records and then sample one `theta`, ten `zerocheck_point` coordinates, and `mu`. They receive no initial claim or eta.

`begin_state_only_masked_sumcheck` is frozen `crates/aspis-core/src/state_only_hiding.rs`, SHA-256 `18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f`. Lines 375–389 serialize the fixed degree/round count with the exact QM31 claim, absorb under `M31_STATE_ONLY_HIDING_MASK_CLAIM`, and call bounded `challenge_nonzero_qm31`.

## Selected terminal and G dependence

The exact selected semantic implementation is frozen `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs`, SHA-256 `13b68f6db428268b2504068d79c88262e36d9abd22fb60e345612eff6e2cd90b` (frozen copy under `frozen-r117/`). In the selected masked-terminal macro, lines 1398–1421, `terminal_parts` returns `original,c1,mask_only,g`, then the function returns

`state_only_selected_mask_value(&c1, &mask_only, g, point) + eta * original`.

The exact `composition_parts` body (lines 1215–1282) uses `g` only as a returned field; `terminal_parts` builds `original` from `composition` and `mu*h1_z`, then returns that `g` with `c1` and `mask_only`. The masked-terminal wrapper puts that returned `g` into the eta-independent mask-value call, while eta scales `original`. The selected build flags enable the positive-transfer branch: frozen `performance_verifier.rs` lines 117–130 adds `positive_transfer::terminal_delta(..., eta)`. Its exact frozen R117 source is copied to `frozen-r117/docs/research/v8-no-work-100-20260907/experiments/positive_transfer.rs`, SHA-256 `3a19043d2f40f168cb2127ba46e1795db7ea0751625c4fe48c73e02dab533cab`; `terminal_delta` at lines 91–92 is `eta.mul(equality(z,zc).mul(composition_delta(claims,z,theta)))`. The R555 diagnostic copy has the same hash. It is another eta-scaled term, but not the G-mask input.

The original retained `payment_extraction.rs` at SHA-256 `957060c7556d2a0365c1cb3d2bf0576a72399c6c20bfbb47ea531f110dba54f5` is in `frozen-r117/`. The R555 diagnostic helper is a distinct file, copied to `r555-diagnostic/payment_extraction.rs`, SHA-256 `703148073c8f70257fc7ff87c823e0a28bff9d96febdf32274e8779998401090`. In R555, `terminal_with_g` at lines 49–53 builds point claims from the supplied G vector and forwards them to `payment_terminal`. That wrapper passes `s.eta` to the selected masked terminal, then applies its extra G-coordinate adjustment `value - claims[27]*state_only_explicit_g_mask_factor(z) + claims[27]` (lines 36–47); with the pinned positive-transfer feature it also adds the eta-scaled positivity term. This is diagnostic helper behavior, distinct from the selected source terminal definition.

## Honest-prover source facts and their boundary

The exact frozen prover source `crates/aspis-prover/src/state_only_hiding.rs`, SHA-256 `0e8b83d50aaebc65dad86bc63c838d099428a166221990156b9f61164148fe0a`, is copied under `frozen-r117/`. `state_only_initial_mask_claim` at lines 837–875 computes a claim by summing `state_only_selected_mask_value` over all Boolean rows from the trace C1, mask-only C1 and G inputs; malformed lengths return `TraceShape`. `prove_masked_state_only_zerocheck`, lines 895–950, checks `RootsNotBound`, computes this claim, samples eta, and supplies `mask(point) + eta*original(point)` to the generic sumcheck producer. Thus the frozen honest producer derives a particular claim from its mask/column values after the precommit binding; this is not a rule restricting arbitrary verifier input. This source-generation fact is not a malicious-prover restriction and does not license dismissing arbitrary verifier input mutation. Whether any modified claim plus adapted messages passes the frozen verifier remains open.

That producer's generic `prove_state_only_sumcheck_from_claim` (frozen `crates/aspis-prover/src/state_only_zerocheck.rs`, SHA-256 `d78eacc5dc05cb5d8991358626a43214b849ca8bbda61f25615f7851984aab84`, copied under `frozen-r117/`) explicitly rejects boundary mismatch and terminal mismatch. Those producer errors must not be attributed to the selected compact verifier, which derives its omitted coefficient. The producer's call closure does keep the mask oracle independent of eta and multiplies the original oracle by eta; the helper does not replace the selected verifier's semantic wire.

No source fact found here says that eta affects the already supplied C1/C2 roots or the earlier `lambda,chi,theta,zc,mu`; no source fact here says a prover can freely change the initial claim while retaining valid proof messages. In particular, the honest claim helper's deterministic computation is evidence about source generation only, not a malicious-prover restriction.

## Source-side commitment schedule (separate from the compact callback)

The frozen `crates/aspis-prover/src/state_only_spend.rs` is SHA-256 `51dfcc84f8155e6db302f112f75914070fc4e99efe972ba06c8e99209604c032` and is copied under `frozen-r117/`. This is the state-only spend prover path, not the selected `performance_verifier` callback. Its exact order at lines 575–638 is: form the C1 tree from trace semantic columns plus `applied.mask_only_c1`, commit/absorb its root, derive `lambda,chi`, build H1 and apply H1 padding, form C2 messages including H1 and `applied.g`, build/absorb the C2 root, sample zerocheck challenges, then call `prove_masked_state_only_zerocheck`. That call computes the initial claim from trace/mask/G and only then samples eta. In this path H1 is computed from `trace,lambda,chi` before C2 root; eta is not an input to it. This supports a source statement about this prover path only; it does not substitute for binding any separately selected host-callback chronology.

## HashFn work per candidate claim

Frozen transcript implementation `crates/aspis-core/src/transcript.rs`, SHA-256 `451357c6d61e3eaf750ead4bc4f3aa5d32db9771346d798818dd331d755bb546`, copied under `frozen-r117/`, lines 316–357: each absorb is one HashFn invocation; each `squeeze_block` calls the HashFn twice (squeeze output, then state advance). Lines 378–429 show bounded noncanonical-limb rejection in `challenge_qm31` and bounded zero rejection in `challenge_nonzero_qm31`.

For a candidate claim starting from the fixed post-`mu` transcript state, its claim absorb costs one HashFn invocation. Eta sampling costs at least two, plus variable extra block hashes if limbs reject or eta is zero; exhaustion is an explicit sampler error. To obtain the first semantic round challenge, its compact round record is then absorbed (one invocation) and the challenge costs at least two more. Thus the minimum is four invocations before sampling the first semantic coordinate and six through that sample; all retries raise the count. This is the suffix cost only. It excludes replaying the prefix from transcript initialization and does not count Merkle root construction. Feature flag `v8_positive_transfer` also changes the pre-claim profile absorb, but that is fixed across candidate claims under the pinned build.

## Verbatim source excerpts

From frozen selected `performance_verifier.rs` lines 43–52 (the verifier receives `w.v[0]` as data; these lines are exact):

```rust
let lambda=sample(&mut t,false)?;let chi=sample(&mut t,false)?;
t.absorb(label::SECOND_PHASE_ROOT,&w.roots.1);
let bat=begin_state_only_zerocheck(&mut t).map_err(|_|Error::Sampler)?;
let eta=begin_state_only_masked_sumcheck(&mut t,w.v[0]).map_err(|_|Error::Sampler)?;
let mut s=row::Semantic{t,z:[K::ZERO;10],lambda,chi,theta:bat.theta,zc:bat.zerocheck_point,mu:bat.mu,eta,claim:w.v[0]};
for r in 0..10 {
    let sent=&w.v[1+27*r..1+27*(r+1)];
    let mut record=vec![r as u8];record.extend(bytes(sent));
    s.t.absorb(label::V6_COMPACT_SEMANTIC_ROUND,&record);
    s.z[r]=sample(&mut s.t,false)?;
```

From frozen prover `state_only_hiding.rs` lines 909–921:

```rust
let initial_mask_claim = state_only_initial_mask_claim(trace, mask_only_c1, g)
    .map_err(MaskedStateOnlyZerocheckError::Mask)?;
let eta = begin_state_only_masked_sumcheck(transcript, initial_mask_claim)
    .map_err(MaskedStateOnlyZerocheckError::Schedule)?;
let sumcheck = prove_state_only_sumcheck_from_claim(
    transcript,
    |point| {
        let mask = state_only_mask_oracle_value(trace, mask_only_c1, g, point)
            .map_err(MaskedStateOnlyZerocheckError::Mask)?;
        let original = original_oracle(point).map_err(|error| {
            MaskedStateOnlyZerocheckError::Sumcheck(StateOnlyZerocheckProveError::Oracle(error))
        })?;
        Ok::<_, MaskedStateOnlyZerocheckError<E>>(mask.add(eta.mul(original)))
```

From frozen selected semantic terminal lines 1410–1420:

```rust
let (original, c1, mask_only, g) = terminal_parts(
                $convert(public, transition),
                claims,
                point,
                lambda,
                chi,
                theta,
                zerocheck_point,
                mu,
            )?;
            Ok(state_only_selected_mask_value(&c1, &mask_only, g, point).add(eta.mul(original)))
```

## Exact frozen artifacts and hashes

* Selected verifier `performance_verifier.rs`: `d6dad89eaa8d735f467055e96a8df12de7a391e2475ec26c44b2bc493624a62a`.
* Selected `relation_callback.rs`: `4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`.
* Core state-only hiding: `18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f`.
* Core state-only sumcheck: `5458d3134a3123b8b02bef0374ccbf96a05461974d7e274966c6a3f0d2d496f9`.
* Core transcript: `451357c6d61e3eaf750ead4bc4f3aa5d32db9771346d798818dd331d755bb546`.
* Prover state-only hiding: `0e8b83d50aaebc65dad86bc63c838d099428a166221990156b9f61164148fe0a`.
* State-only spend prover path: `51dfcc84f8155e6db302f112f75914070fc4e99efe972ba06c8e99209604c032`.
* Selected pair-forest semantic terminal: `13b68f6db428268b2504068d79c88262e36d9abd22fb60e345612eff6e2cd90b`.
* Frozen original `payment_extraction.rs`: `957060c7556d2a0365c1cb3d2bf0576a72399c6c20bfbb47ea531f110dba54f5`.
* R555 diagnostic `payment_extraction.rs`: `703148073c8f70257fc7ff87c823e0a28bff9d96febdf32274e8779998401090`.
* Frozen R117 `positive_transfer.rs`: `3a19043d2f40f168cb2127ba46e1795db7ea0751625c4fe48c73e02dab533cab` (same bytes as R555 diagnostic copy).

The snapshot bytes remain retrievable under `.r21-scratch/r563-initialclaim-dependency/frozen-r117/`. No grinding, additional claims, or runtime tests were attempted.
