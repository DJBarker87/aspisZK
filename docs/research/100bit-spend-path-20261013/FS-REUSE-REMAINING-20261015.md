# Remaining Fiat–Shamir reuse obligations

This is a theorem-interface inventory for the current conditional R1
Fiat–Shamir development. It records what the checked results require; it does
not instantiate the missing premises or claim protocol closure.

The user subsequently clarified **100-bit per-attempt soundness without
grinding credit**; see [the target record](TARGET-CLARIFICATION-20261015.md).
The absolute full-experiment `Q` scenarios below remain useful disclosures,
but are not the numerical acceptance criterion for that clarified target.

The current composition is [`UnifiedFiatShamir.soundness_bound`](lean/UnifiedFiatShamir.lean).
It applies the unchanged `R0C.V3.theorem43` to the 33-round unified protocol.
Its explicit inputs include `Params` with `5 ≤ p.D`, public byte length below
`2^32`, all 33 label equalities, an encoding of the empty row-zero record, an
extractor, a Boolean decision, and a `RoundByRound'` classifier. It also
requires:

- `hD1 : FS2.D1 protocol rb`;
- `hD2 : FS2.D2 protocol rb`;
- `hD3 : FS2.D3 protocol rb verifier`;
- for every oracle `H`, `distinctFirstReads` of the full prover-plus-verifier
  experiment is at most `Qtot`.

The conclusion is conditional:
`Qtot * maxErr rb.ε 33 + 3 * Qtot^2 / 256^32` bounds acceptance together with
extractor failure. `UnifiedChainDensity.chainDensity` derives the framework's
`ChainDensity3` interface from the explicit D2 premise; it does not prove D2.
Its `decoded_bound` step still needs a fixed-context row bound for every
successful decoded context and every completion list of the exact required
length.

The relevant legacy interface is `R0C.V3.theorem43` in
[`Gen.lean`](../v8-r0-close-20261007/lean/R0C/V3/Gen.lean). It requires D1,
`ChainDensity3`, D3, `ChainsRead`, `ReadsChains`, `Inj3`, and the same `hQ`
bound on distinct first reads. Its conclusion is
`Qtot * maxErr rb.ε pr.r + κ Qtot`. The linear multiplier is part of this
existing theorem interface: the proof obtains a first-read union bound from
`hQ`. The checked old R0FS/V3 theorem inventory has no stronger Q-free or
work-normalized reduction that removes it.

The q22 result reused by the current row-31 sampler is
`R0C.V3.Q22.q22_bound` in
[`Q22Law.lean`](../v8-r0-close-20261007/lean/R0C/V3/Q22Law.lean). For a fixed
set of size at most 9,557, it bounds the event that the output 22-set lies in
that set after eight independent state-pair steps by
`C(9557,22)/C(262144,22)`; exhaustion contributes zero. The legacy global
`r0_q22_fiat_shamir_closed` theorem in
[`R0Q.lean`](../v8-r0-close-20261007/lean/R0C/V3/R0Q.lean) still carries the
factor `Qtot` and a collision term. In the current R1 route, `UnifiedQueryLaw`
proves the exact sampler-law identity, and `UnifiedDecoderBound` transfers an
explicit fixed-completion bound. Neither proves the required fixed-context
q22 bound from the concrete classifier/decoder on all contexts; that remains
part of the D2 instantiation.

The arithmetic profile in [`FS-BUDGET-PROFILE.md`](FS-BUDGET-PROFILE.md)
evaluates `B(Q) = Q * max_row + 3*Q^2/2^256` using the current ledger's
`max_row ≈ 2^-105.136475`. The largest integer budget meeting
`B(Q) ≤ 2^-100` is 35; at 36 the bound exceeds `2^-100`. This is a limit of
the stated conditional formula, not a measured full-experiment query bound
or an impossibility result. The observed 583 verifier raw calls and the
single-run 452 distinct-input measurement do not establish `hQ`: they are not
an adversarial upper bound on distinct first reads of the full experiment.

Accordingly, the concrete D1/D2/D3 instance, a full-experiment `Qtot` bound
compatible with the desired numerical target, and source/account/privacy
correspondence remain open. No work or grinding credit is assumed.

## Direct causal route added on 15 October

[`UnifiedCausalBound`](lean/UnifiedCausalBound.lean) now reuses the existing
V3 `lemmaA3` directly with the current unified background decoder. For an
arbitrary event on the decoded prefix, message, pre-read table and challenge,
a uniform bound `B` on each fixed-row sampler implies a total first-hit bound
`N * B`, under an explicit cap of `N` distinct first reads. Both the lazy
experiment and empty-oracle mean versions compile. This includes the
background laws for initial, reseed and query samplers; it needs no D1/D2/D3
classifier. [The exact inventory](CAUSAL-FIRST-HIT-REUSE-20261015.md) records
the theorem and premises.

This supplies an alternative probability-accounting route. Concrete row
predicates and their density bounds, causal recovery of their committed
words, and acceptance implying a hit or successful extraction remain to be
proved. The `N` factor remains; the theorem does not convert an arbitrary
oracle-query budget into a single transcript attempt.


## Fixed-context density adapters now checked

The direct causal route now has explicit event-family adapters:

- [UnifiedSemanticDensity](lean/UnifiedSemanticDensity.lean) reuses the old
  25 semantic rows at indices 0–24 and their individual row budgets.
- [UnifiedOpeningDensity](lean/UnifiedOpeningDensity.lean) handles gamma,
  kappa and both fold challenges at rows 27–30, with degree-at-most-six
  polynomial guards in its decoded context.
- [UnifiedQueryDensity](lean/UnifiedQueryDensity.lean) proves the row-31
  density for a pre-challenge decoded set with an explicit cardinality guard
  of 9,557 and successful 22-element sampler output. It reuses `q22_bound`
  through the current background sampler law.
- [UnifiedRhoDensity](lean/UnifiedRhoDensity.lean) handles the row-32 residual
  event using the specified encoded modulo sampler and the existing 21-root
  theorem.

The opening/query/rho adapters also instantiate the generic causal first-hit
bound. None asserts that its arbitrary callback is the callback supplied by
an accepted Rust proof. The next interface is equality of the causally
recovered contexts with the authenticated words and parsed messages consumed
by the deterministic extraction theorems, followed by an acceptance-to-hit
implication. Circle values do not require an OOD uniqueness event in the new
joint-list argument; this observation still needs to be reflected in the final
concrete classifier. Hash-collision and root/child prediction events must also
remain in the full experiment's accounting.
