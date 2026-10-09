# Component recovery through the actual OOD constraints

Parent: `9254b2416c3f8c3c488d0475a00d812fee836e00`, on the existing
`research/v8-no-work-100-20260907` branch. Research only. All new Lean checks
ran serially on the NUC; none ran on the laptop or modified production.

## What changed

The retained good-quotient case now has a **new quantitative restriction**,
derived from the same execution's committed components and actual OOD
answers. It does not require a recovered tuple or a successful decoder.

Choose one nonzero V7 trivariate interpolation polynomial
`P(X,Y,Gamma)` from the fixed 29 received component words, before either
OOD point or answer. For the two actual OOD points, form the actual
normalized answer polynomials `A_r(Gamma)`, each of degree at most 28.
Define

```
R_r(Gamma) = P(t_r, A_r(Gamma), Gamma).
```

Every image-valid quotient in the literal 9,558-fibre family forces
`R_0(gamma)=R_1(gamma)=0` at the actual gamma, even when the quotient is
selected after gamma or the first folding challenge. If either fixed
polynomial `R_r` is nonzero, at most **117,077 gamma values** can qualify.
No candidate-family multiplier or factor of two is needed.

The complementary case `R_0=R_1=0` as polynomial identities is retained.
It is not declared rare, recovered, or a valid payment witness. This is a
reduction of the remaining component-recovery obligation, not its completion.

For the actual compact causal game, the new checked composition is

```
totalProbability
  <= previousMissingGoodCeiling + 117077/|GammaSet|
     + if bothSymbolicOODIdentities then goodProbability else 0.
```

With ideal uniform nonzero QM31 gamma, the new component term has a display
value of **107.162901839394 bits**. Added to the existing missing-good
ceiling, the local reduction ceiling is **104.366053135544 bits**, with
the remaining identity-branch mass explicit. Exact rational comparison,
not a floating-point display, checks that this ceiling is below `2^-100`.
It is **not** a global accepted-extraction or Fiat–Shamir security bound.

## The deterministic chain is actually connected

1. A literal quotient-family member matches at least 9,558 complete fibres:
   38,232 distinct stored symbols. The exact child-index map is used.
2. The checked nondegenerate chord has at most **two pole symbols**. Removing
   those symbols, rather than two entire fibres, leaves at least **38,230
   actual original-code agreements**. This crosses V7's strict 38,229
   threshold. No global received-word polynomiality or global nonpole
   premise is used.
3. The same image-valid Q reconstructs the original natural1024 message
   `U = LQ+I`. `CoveredOriginalSymbols.selected_width29_valid` constructs
   the exact V7 valid-response interface for U, including the original
   scalar-power batch and support orientation.
4. Reuse
   `V7ExactCorrelatedAgreement.exactInitialValidCandidate_substitute_eq_zero`:
   the GRS polynomial of U is a root of `P_gamma(X,Y)`. The candidate is
   not fixed before gamma; the theorem uses its actual agreement support.
5. At each actual OOD circle point, `CoveredOODGRS.original_grs_at_ood`
   proves the precise normalization:

   ```
   GRS(U)(t_r) = (1+t_r^2)^512 * actualBatchedOODAnswer_r,
   t_r = y_r/(1+x_r).
   ```

   This is proved at arbitrary legal OOD points, not inferred from stored
   evaluation points. The multiplier is a **multiplication**, not division.
   The checked interpolant includes its equal-x branch. Circle membership
   and `x_r != -1` remain explicit source/sampler hypotheses.
6. Substitute these actual values in the same interpolation polynomial.
   V7's weighted monomial condition is `h+28*j < 117078`. Therefore the
   whole OOD substitution has degree at most 117,077. There is no additional
   `28*111` degree charge: that weight is already included in the bound.
7. The generic polynomial-root theorem counts all compatible candidates
   together. The actual `CausalCoveredRecovery.Execution` wrapper then
   derives the bound on its retained good-quotient acceptance mass and
   composes it with the previous missing-good theorem.

The pre-OOD interpolation polynomial is a noncomputable mathematical
choice supplied by the existing V7 finite-dimensional existence theorem.
No matrix is materialized. This is not an efficient list decoder or a
claim that the extractor can construct that enormous coefficient vector.
The old approximately 75-bit full recovery loss is not imported.

## Causal and total-event accounting

| Boundary | Objects fixed or conclusions available |
| --- | --- |
| C1 commitment, before lambda/chi | Actual C1; the previous early C1 family remains fixed here |
| After permitted C2 commitment | C2 may depend on lambda/chi; both words now determine P before OOD |
| Sequential OOD point0/answer0, then point1/answer1 | The second response may depend on the first; both normalized answer rows precede gamma |
| Fresh ideal gamma | Both `R_r` are already fixed; one nonzero row bounds their common compatible gamma set |
| Kappa/tau, response0, alpha0/final | The actual quotient representative may be selected adaptively; root implication holds for every representative |
| Queries/rho/later responses | Actual compact suffix remains unchanged; old theorem already charges scalar-only acceptance and relation repairs |

The new prefix predicate is determined **before gamma**, so it may be
retained as an indicator when averaging arbitrary causal OOD prefixes.
We do not condition on successful recovery, on a favorable query schedule,
or on an OOD identity and then assume the old challenge law remains uniform.
The present theorem fixes the prefix and assumes the ideal fresh gamma law;
the outer source/replay/FS law remains to be connected.

For the eventual specified bounded extractor X and complete acceptance A,
use this precedence on the compact-game part of `A AND NOT X`:

| Class | New status |
| --- | --- |
| No good quotient representative | Previous ceiling reused, not replayed or counted again |
| Good quotient; at least one OOD substitution nonzero | Newly bounded by `117077/(k-1)`, uniformly over all subsequent strategy choices |
| Good quotient; both substitutions identically zero; extraction fails | Explicit remaining mass; no numerical bound assigned |

The checked `total_reduction` is stronger than the corresponding restriction
to extraction failure because it bounds all compact acceptance in the first
two classes. It does not define X, solve authenticated access/list generation,
or prove the complete payment/source acceptance theorem. Source/authentication
mismatches, replay/fuel/abort/provider-none outcomes and literal validator
failure still need coupling to the chosen extractor. Success through any
valid alternative witness remains success, including minority candidates.

## What the identity case does not imply

Nonzero P does not guarantee a nonzero `R_r`. Honest component curves can
make both substitutions identically zero. Nor do two identities alone
construct a coherent component curve.

A small algebraic countermodel to that latter shortcut is
`P=(Y-Gamma)(Y-2*Gamma)` with answer curves `Gamma` and `2*Gamma` at two
distinct X points. Both substitutions are identities. For nonzero gamma,
over a field of characteristic other than two, a polynomial candidate
satisfying `P(X,U(X),gamma)=0` must be the constant gamma or the constant
2*gamma, and cannot match both answers. This is a pencil-and-paper generic
factor argument, independently reviewed by an agent, **not a selected-word
kernel counterexample or a payment forgery**. It warns against dropping the
actual compatible-candidate and received-kernel information in the next
theorem. The current remainder retains both.

Existing regressions were not rerun because their implementations are
unchanged. Original/paired root products remain allowed in the unresolved
component accounting; their failed same-support shortcuts are not restored.
High-J and mixed-C1 cases can remain in the identity branch with own-support
or alternative candidates. T512 invalid image stays in the already charged
missing-good branch. Zero-fold image loss, shifted cubic rows, late-inactive
timing, shifted degree-q query cancellation and later repairs are unchanged.
Radius failure is still not extraction failure.

## Payment-copy bridge completed in parallel

The [selected layout continuation](selected-copy-layout-review.md) freezes
the actual 136 producer/consumer endpoint triples and 14 tuple patterns.
The exact 272 endpoint placements are inside the selected active-row mask.
From that source-shaped construction, Lean now derives the previously
caller-supplied `inactiveWeights` condition and consumes the existing
whole-table weighted rational balance theorem.

All four denominator-pole conditions remain, including zero-weight slots.
Local residuals and total/inactive helper boundaries remain substantive
prerequisites; they are not assumed consequences of acceptance. Endpoint-slot
uniqueness, row-to-link rational sums and collision-explicit weighted aliases
are the next deterministic source obligations. This does not finish the
literal transfer validator or prove early semantic root counts for a tuple
chosen after adaptive C2.

## Theorem, evidence and cost status

| Leaf | New checked consequence | Green NUC wall / peak RSS KiB |
| --- | --- | --- |
| `CoveredOriginalSymbols` | Actual quotient-to-original support and V7 valid-response interface | 3.23 s / 6,856,640 |
| `CoveredOODGRS` | Actual original-message OOD-to-GRS normalization | 10.89 s / 6,838,648 |
| `CurveOODGate` | Weighted OOD polynomial degree and adaptive existential root count | 2.94 s / 6,831,432 |
| `SelectedOODGate` | Same selected Q forces both actual OOD substitutions to vanish | 4.60 s / 6,867,636 |
| `CausalOODReduction` | Same-execution good-mass bound and explicit identity remainder | 3.32 s / 6,879,464 |
| `SelectedCopyLayout` | Literal endpoint/mask and pattern-range certificate | 2.36 s / 1,913,972 |
| `SelectedCopyLayoutRows` | Constructed row balance without assumed inactive weights | 0.87 s / 1,731,268 |

All green jobs exited zero with zero swaps; 41 named endpoint/helper axiom
audits are standard-only. These are kernel-checked algebraic/source-shaped
interfaces, **not a Rust-to-Lean translation of the complete verifier**.
See [build provenance](component-cover-build-evidence.md),
[support and OOD source review](covered-original-symbols-review.md),
[machine evidence](component-cover-evidence.json), and the
[event/rational ledger](component-ood-ledger.json).

The NUC reused the pinned native Lean4.32/Mathlib cache and a fresh overlay,
with MemoryHigh8GiB, MemoryMax10GiB, MemorySwapMax0, CPUQuota200%, Lean
`-j1 -M9500`, one own compiler job at a time. No cold dependency build,
unchanged full replay, giant field enumeration or SBF rebuild occurred.
Failed preflights and their hash-matched exact sources are retained:
the GRS specialization needed symbolic opaque arguments and two narrowly
scoped recursion-depth400 type-specialization applications; no heap or
heartbeat limit was raised. The selected OOD wrapper used named V7 parameter
types and explicit sparse projection simplification. The final causal leaf
needed an explicit natural-to-rational cast normalization. Failed diagnostics
are not counted as green proofs.

Reproduce only the changed focused target after its recorded dependencies:

```sh
ssh -o BatchMode=yes dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo/run_component_cover_nuc.sh /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo CausalOODReduction new-unique-tag'
python3 docs/research/v8-no-work-100-20260907/experiments/audit_component_cover_evidence.py --check-recorded
python3 docs/research/v8-no-work-100-20260907/experiments/component_ood_ledger.py --check-recorded
```

The body remains `697*16+52+24+22*621+2*296*26 = 40,282` bytes.
New public messages, verifier operations and proof-body values: zero.
No new CU, prover-time or executable-extractor measurements were made.
Full-view ZK and resource-bounded Fiat–Shamir remain independent gates.
There is no grinding credit, no quantitative quantum claim, and no invented
probability for missing source/toolchain assumptions.

## Decision and next experiment

QM31 q22 still deserves priority. This continuation uses existing V7
mathematics to bound a genuine new part of the arbitrary-oracle remainder,
without changing the proof grammar or the selected performance profile.
It does not establish production readiness or the global100-bit contract.

The decisive next experiment is **coherent component coverage inside the
paired symbolic-OOD-identity branch**, using the actual interpolation kernel,
the compatible original candidate and the sequential OOD fixing boundaries
together. Seek a code-valued degree28 component curve whose C1 projection
belongs to the pre-lambda family, or a charged exception with a justified
finite bound. Do not replace that task by proving the identities again or
assuming that two individually selectable algebraic branches coincide.
Keep alternative C1 candidates, degree-two helper reduction where genuinely
applicable, degree28 claim errors and authenticated extractor resources
explicit. A failure of that implication should yield a precise causal
falsifier, not removal of the accepted identity-branch mass.
