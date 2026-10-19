# Q22 transcript and generic FS inventory

This is a read-only source inventory, not a Rust-to-Lean refinement, protocol
proof, or gate closure. The Lean probability statements below describe the
formal independent-answer challenge model. The Rust source is listed separately
because no refinement connecting its concrete shared-oracle transcript to that
model was found in the inspected repository.

## Bounded ordered-injection query sampler

The Rust implementation is in [`r0_transcript.rs`](../../../crates/aspis-core/src/r0_transcript.rs).
It samples eight 32-byte transcript blocks, takes eight little-endian `u32`
words from each, and masks each word by `2^18-1`. `QueryScan::scan` consumes
words in order, counts duplicates against the 64-word budget, and appends only
new query indices. It reports completion after 22 distinct indices. Exhaustion
before 22 distinct indices returns `DrawLimitExhausted`; the caller rejects.
`Transcript::r0_challenge_queries` allows up to eight squeeze/advance pairs,
with each pair supplying eight words; it propagates exhaustion as an error.
`queries_from_pairs` is a deterministic helper over supplied block/advance
arrays, not a probability-law or source-refinement theorem.

The formal candidate program in `AspisV8R19.Q22SamplerProgram.challengeProgram`
and bounded word scanner model the same high-level loop: up to eight blocks,
eight words per block, unique indices only, 22 accepted indices, and a maximum
of 64 draws. The exact-law result is stated by
`R0C.QuerySource.successful_subset_exact`:

```lean
independentMean (Q22SamplerProgram.challengeProgram s)
  (fun v => containsOnly M v.2.1) =
  successMass 8 * ((M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ))
```

Here `containsOnly` is zero on every `.error` result and indicates that every
successful returned index lies in `M`. `successMass 8` is the probability mass
of a successful scan under the formal candidate kernel. Therefore the theorem
is an **unconditional successful-event subprobability**. Exhaustion/rejection
mass remains outside the event; the theorem does not condition on success and
does not divide by success probability. `successMass_le_one` yields
`successful_subset_le`, which bounds this unconditional mass by
`C(|M|,22)/C(262144,22)`.

`R0C.QueryCounting.subset_mean` supplies the ideal ordered-injection
combinatorics: a uniformly distributed ordered injection of 22 distinct
elements from a universe of size `2^18` lies entirely in `M` with probability
`C(|M|,22)/C(2^18,22)`. `AspisV8R19.R417Q22SuccessLaw.uniform_success` factors
the candidate-kernel observer into `successMass n` times a uniform mean over
legal ordered injections, provided the observer is zero on errors. The finite
candidate bound `R0C.V3.Q22.q22_bound` converts a matching set of size at most
9557 into the conservative bound `C(9557,22)/C(262144,22)`.

For this Q22 exact law, `delta0` is not needed. The separate legacy scalar
sampler envelope `R0C.SlackStatement.delta0 = 257 * P^8 / 256^32 - 1` is a
conservative modulo-sampling bound and should not be confused with the exact
unconditional Q22 successful-event law.

The stopped-state mechanics are explicit in `R0C.V3.Q22.chainE_scanOut`, which
equates `chainE` over the eight-step scan with `independentMean` over the formal
loop program. `R0C.V3.DQ.decodesQ` is the R0 query-specific decoder bridge for
the 5-round protocol. The supporting stopped-chain facts are in
`R0C.V3.DQChain`: `st_succ'`, `runOut_chainBS`, `chainS_reads`, and
`chainS_out`. `round_q22_bound` in `R0C.V3.DuplexQ` maps the matching-fibre
cardinality premise into the existing R0 round bound.

### Distinction from conditional and delta-based bounds

The exact theorem has a multiplicative success factor and counts failed scans
as zero, so it is already an unconditional successful-event probability. The
corollary drops only a factor known to be at most one. It is not a theorem about
the conditional distribution given successful sampling. The scalar-sampler
`delta0` envelope concerns a different abstraction and is unnecessary to state
the exact q22 law.

## Shared-oracle and first-read obligations

The generic FS2 framework is in `docs/research/v8-fs-generic-20261006/lean/FS2`.
`FS2.D2` (`Statement.lean`) is exactly:

```lean
def D2 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A) : Prop :=
  ∀ (i : Nat) (P : Prefix X M C) (m : M) (T' T : Table I A),
    P.round = i → i < pr.r → rb.doomed P T' →
    independentMean (pr.samp i P m).toProgram
      (fun w => indicator (¬ rb.doomed (P.ext m w.2) T)) ≤ rb.ε i
```

This is a stopped-state condition: for every prefix
whose current round is `i`, if the state is doomed and `i < pr.r`, the
independent fresh-answer mean of not-doomed extensions is at most `ε i`.
`FS2.Duplex.chainDensity` (`DuplexDensity.lean`) consumes this `D2` premise to
obtain the generic chain-density bound. `FS2.Duplex.decodesSpec`
(`DuplexDecodes.lean`) requires a bound `hQ` on the number of distinct
first-read addresses in each verifier execution; outside the collision event,
it shows every first chain-cell read decodes to the intended round sampler and
follows the trace to the transcript prefix, message, and challenge.

The declarations have these exact theorem heads (with the surrounding section
variables implicit):

```lean
theorem FS2.Duplex.chainDensity
    (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
    (extract : X → Table (Addr L) State → Option W)
    (rb : RoundByRound' X M (Chal Cv) (Addr L) State)
    (hD2 : FS2.D2 (protocol p x msg extract) rb) :
    ChainDensity (protocol p x msg extract) rb

theorem FS2.Duplex.decodesSpec
    (hQ : ∀ H, distinctFirstReads (eval H (experiment P (V) x)) ≤ Qtot) :
    DecodesSpec p x msg extract P (V) Qtot
```

The R0-specific decoder signature is `R0C.V3.DQ.decodesQ`: with `hr5`,
`hQ`, a concrete oracle `H`, non-collision premise `hcoll`, round `i < prQ.r`,
and a `firstCell` witness, it returns `own`, `pend`, and `g` such that `decQ`
returns those values and `bfollow g (traceFrom ...)` yields the exact protocol
transcript prefix, message, and challenge at round `i`. Its complete dependent
signature is in `R0C/V3/DQDecodes.lean:183` and is indexed in the JSON manifest.

These are address-sensitive because the duplex protocol shares an oracle.
Reads made before a challenge, reads by other parties, reused addresses, and
background reads can affect whether an address is already fixed at the relevant
first read. The generic multi-read sampler and the Q22 stopped sampler must
therefore account for the actual first-read order and for all spawned squeeze
and advance cells. The Q22 path uses an explicit spawned/background-read
construction (`R0C.V3.DQ` and the `BS` chain) because the next stopping decision
depends on earlier squeeze answers even though later advance addresses may
already be addressed. The formal bounds charge the applicable read budget; they
do not by themselves establish that the R1 Rust transcript or the shared
production oracle satisfies those premises.

No Rust refinement theorem was found connecting `QueryScan::scan`,
`Transcript::r0_challenge_queries`, or `queries_from_pairs` to the Lean
`Q22WordScan.scan`, `scanOut`, or `challengeProgram`. The Lean result is thus
evidence about the formal model only; source-to-model correspondence remains an
independent obligation.

The generic R0 masked route also has explicit semantic decoder premises.
`R0P.SemD2Glue.combinedProtocol_D2` constructs the 31-round combined-protocol
`D2` premise only from the per-challenge `hσsem`, `hσz0`, `hσz1`, and `hσopen`
decoder assumptions. `R0P.MaskDuplexDensity.combinedChainDensity_of_D2` then
consumes a combined `D2` premise. `R0P.MaskDuplexChain` records the stopped-state
chain equations and read/output maps (`st`, `st_succ'`, `runOut_chainBS`,
`chainS_reads`, `chainS_out`). These signatures are listed for locating source
facts; this inventory does not assert their premises for R1.

The rowwise 31-round assembly has theorem head:

```lean
-- The sampler result type is abbreviated here; the full declaration is at
-- SemD2Glue.lean:1427.
R0P.SemD2Glue.combinedProtocol_D2
  (B : PackBasis (Sfield 0))
  (p : Duplex.Params (Msg WideExact WideExact (SemMsg WideExact))
    (Chal WideExact WideExact) L)
  (msg : Pf → Nat → Msg WideExact WideExact (SemMsg WideExact))
  (decode : Addr L → Table (Addr L) State → Option (FS2.Sampler ...))
  (hσsem : ∀ i (_hi : i < 24) s, p.σ i s = Chal.semantic (semChal s))
  (hσz0 : ∀ s, p.σ 24 s = Chal.circle (circleSample0 s))
  (hσz1 : ∀ s, p.σ 25 s = Chal.circle (circleSample1 s))
  (hσopen : ∀ j : Fin 4, s, p.σ (26 + j.val) s = Chal.opening (DQ.σQ j.val s)) :
  FS2.D2 (R0P.SemD3Glue.combinedProtocol B p msg decode)
    (R0P.SemD3Glue.duplexRows B combinedD2Budget)
```

Its `combinedD2Budget` assigns the semantic-round candidate budgets to rows
0–23, the two circle-row bounds to rows 24–25, four field-opening bounds to
rows 26–29, and the q22 bound to row 30. In the masked 32-round variant,
`R0P.MaskD2Instance.combinedProtocolZ_D2` has analogous per-row sigma premises
for semantic rows 0–24, circle rows 25–26, and opening rows 27–30; it concludes
`FS2.D2 (combinedProtocolZ ...) (duplexRowsZ ...)`.

The row-transport step used after a D2 proof is stated as
`R0P.SemDuplexDensity.combinedChainDensity_of_D2` for the original 31-round
protocol, and as `R0P.MaskDuplexDensity.combinedChainDensity_of_D2` for the
masked parameterized protocol. Each takes an explicit `FS2.D2` premise over
the corresponding protocol and row predicate, then returns the matching
`ChainDensity3` for its combined decoder. No claim is made here that an R1 row
predicate, stopped-state invariant, sigma map, or decoder instantiates these
premises.

## Broad tactic import footprint: source-use suggestions only

`AspisV8R19.OracleResampling` imports `Mathlib.Tactic` but visibly uses only
ordinary `simp`/`rw`/congruence, `exact_mod_cast` once in `mean_const`, and
`ring` once in `mean_prod`. The narrow candidate for `ring` is
`Mathlib.Tactic.Ring`. The exact-cast tactic did not have a discoverable
standalone definition in the inspected Mathlib tactic sources; avoid guessing
an import replacement. A direct cast proof or a focused import diagnostic in
the pinned environment is needed before changing the broad import.

`AspisV8R19.DuplexFrames` imports `Mathlib.Data.List.OfFn` and `Mathlib.Tactic`.
Its only non-core tactic use is `omega` in `absorb_disjoint`; the pinned Mathlib
source shows the tactic integration in `Mathlib.Tactic.Order`, which imports
Lean's Omega elaborator. Ordinary `simp`, rewriting, and list operations do not
indicate a need for the rest of `Mathlib.Tactic`. These are candidate import
reductions only; this document did not edit imports or compile replacements.

## Source manifest

`QUERY-FS-INVENTORY.sources.json` records the inspected Rust/Lean source paths
and SHA-256 values. Hashes identify the local source snapshot only; they are
not compiled-object or release-cache provenance.
