# Fixed early C1, adaptive far finals and extraction

Research branch: `research/v8-no-work-100-20260907`.
Parent revision: `edb199c12fcc41f00330298b95b4736f60ac6f3a`.
Borrowed immutable V7 formal source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
All added files are research artifacts. The profile and verifier source are
unchanged by this continuation.

## Result and decision

The requested fixed-early-C1 far-final reduction is kernel checked. It retains
the three arbitrary helper words as a degree-two curve, the full degree-28
component-claim error, and final256 chosen after alpha. The actual compact
suffix is bounded by its **relation-compatible agreement moment** plus the
shifted query-batch and three later relation collision terms. The remaining
moment is explicit and has no proved small numerical bound.

A separate checked theorem constructs a post-alpha final that zeros the
actual carried prior whenever one folded weight coordinate is nonzero. Its
effect on every query residual is derived. Thus a first-round degree-six
root count against a fixed fold cannot be applied to an arbitrary adaptive
final. This is a restriction on a proposed proof step, not a payment forgery.

The exact F19 causal control also retains the degree-two/degree-28 distinction.
Its optimal far relation-compatible query moments are `7219/73872` and
`21365/221616` for two declared received-word profiles. These results describe
a reduced, restricted family, including abstract tail responses; there is no
QM31 extrapolation. They motivate recovering coherent alternatives across
forks rather than assuming that relation compatibility alone makes every
far branch negligible.

`SevenAlphaRecovery` now proves a deterministic common-support fork
certificate on the selected encoders. Four adaptive branches construct a
quotient; more than 255 common matching fibres identify every other final;
seven actual prior zeros force the shared response's degree-six discrepancy
to vanish. `ThreeTauRecovery` then retains this same quotient across three
tau values and proves the ordinary scalar equality and both zero-image
constraints separately. First responses may depend on tau and final vectors
on tau and alpha; the common support is what ties them together. The
[fork obligations](fork-recovery-obligations.md) record the required replay
access and challenge boundaries. These are deterministic certificates; no
probability of collecting a useful certificate is yet proved.

## Exact causal reduction

`FixedC1FarMoment.Execution` fixes C1 and its optional early identification,
then the adaptive C2 words, both OOD vectors and ordinary component claims
before gamma. Inactive may depend on gamma but precedes kappa. Ordinary weights
and their scalar precede tau; response0 precedes alpha; final256 follows alpha
and precedes queries; queries precede rho; each later response precedes its own
challenge. `Data.Checked`, legal circle points and actual transcript coupling
are source-instantiation obligations, not established by the `Execution` type.

For the actual chosen final let `M` count its matches with the folded virtual
quotient and let `c` be its actual carried scalar discrepancy. The suffix bound is

```
Pr[suffix acceptance and O]
 <= E[1_O * 1_(c=0) * choose(M,q)/choose(T,q)]
    + q/|G| + 18/|A|.
```

`O` is determined at the full pre-query prefix. A stronger supported theorem
weights the last two terms by the mass of `O`; the causal wrapper uses the
displayed conservative bound. The actual query order and degree-q shifted
polynomial are retained. Only the three later degree-six repairs are charged.
The first response, image challenge and row challenge remain inside the moment.

One false C1 claim fixes a nonzero degree-at-most-28 polynomial for every
fixed helper-message triple. Charging its gamma roots gives

```
Pr[farWrong and relation acceptance]
 <= 28/|Gamma| + outsideRootMoment
    + q/|G| + 18/|A|.
```

This last step is bookkeeping until a coverage/recovery argument connects
that helper-message triple to the actual final. It neither proves coverage
nor bounds the unknown moment. In particular, no 100-target union, old
recovery loss, or positive work contribution has been inserted.

## The extraction event still to prove

Let `A` be intended complete repaired-verifier acceptance and let `X` mean a
specified bounded extractor returns a witness passing the authoritative
payment/context/settlement checks. A proof of `Pr[A and not X]` must connect
the following cases in precedence order; this table is an obligation map,
not an already proved source partition.

| First unresolved condition | Required treatment |
|---|---|
| Authentication or fixed-word/source coupling fails | Use the actual hash/oracle experiment, with its queries and failure event |
| Replay abort, fuel exhaustion, missing response, cache/advance mismatch | Charge the specified extractor's concrete outcome; never discard `none` |
| No early C1 object or unsuccessful coefficient reconstruction | Apply an available recovery theorem within its hypotheses, or retain the mass |
| Near-regime bad binding | Reuse the precise supported near theorem after source instantiation; it does not bound the entire near regime |
| Scalar suffix accepts with prior/query discrepancy nonzero | Shifted degree-q rho and three later repairs, counted once |
| Relation-compatible far final | Attempt a coherent quotient/component recovery certificate; bound failures of that specified attempt |
| Recovered coefficients/tuple fail semantic or payment checks | Prove the remaining constraint/early-challenge implication or retain the accepted failure |
| Checked valid witness returned | Contributes zero to `A and not X`, even outside a selected radius cutoff |

The broad `farWrong` event is not identified with `A and not X`. An alternative
recovered polynomial is neither dismissed as a failed early reference nor
declared a valid witness: it must undergo the literal payment checks. The
degree-two helper identity holds on early C1's own support, not on every
received fibre. Reconstructing a quotient from forks alone does not bind each
of the 29 components or justify earlier lambda/chi root arguments.

## Completed dependency map

| New leaf(s) | Checked implication | Remaining connection |
|---|---|---|
| `ChordRationalAlgebra`, `ChordRationalDegree` | Actual four-slot chord adjugate/norm; nonzero cleared discrepancy has at most 257 nonpole plus two pole matches | Raw coefficient lines must meet the polynomial hypothesis |
| `FourPointSubmodule`, `ChordRationalDivisibility`, `ChordRationalQuotientDegree` | Four exact cleared folds construct a common polynomial quotient, with inherited degree bounds | General arbitrary received oracles are not assumed polynomial |
| `ChordRationalOOD`, `ChordRationalBadOOD` | Reconstructed product identity forces both batched OOD values; a wrong value permits at most three exact cleared alpha continuations | Ideal sampling/source composition and component recovery |
| `RationalCoordinates` | Exact affine relation between radial and stored final coordinates, preserving degrees/injectivity | Full selected-domain/source-game constructor |
| `PackedLimbCollect`, `PackedQueryRecord` | Canonical 621-byte record, all lane/limb/index mappings and gamma recombination | Optimized machine parser and observed authenticated word coupling |
| `SelectedAppendAfterstate` | Same-table selected residuals determine append hashes, frontier/root and cursor | Complete payment and runtime-binding endpoint |
| `RelationCompatibleMoment` | Actual causal suffix acceptance reduces to the actual compatible moment | Quantitative accepted extraction-failure bound for that moment |
| `AdaptiveFinalPrior` | Construct a legal post-alpha correction, with exact residual change | Shared-support coherence across forks |
| `FixedC1FarMoment` | Fixed C1, degree-two helpers and degree-28 errors compose with the adaptive suffix | Helper coverage, far recovery and early-C1-none outcomes |
| `SevenAlphaRecovery` | Construct a selected-code quotient and a single-tau relation identity from common support across adaptive finals | Authenticated collection and probability of a useful certificate; component/payment recovery |
| `ThreeTauRecovery` | The same constructed quotient satisfies the ordinary scalar and both image constraints separately across three tau branches | Four-kappa row separation, gamma/component recovery and bounded authenticated fork access |

`NaturalBinaryPolynomial` and `PackedQueryResidual` have retained failed
focused diagnostics. `ChordRationalQueryGame` and `SelectedRationalMatch` are
unbuilt drafts. None contributes a theorem or an error allowance in the
current evidence. Their explicit status is important when navigating files
that contain theorem syntax but have no successful whole-leaf replay.

## Ledger and measurements

The exact local arithmetic file is `experiments/far_moment_budget.py`.
With full-field alpha and nonzero gamma/rho in QM31, the recorded root/suffix
terms sum to `50/(k-1) + 18/k`, where `k=(2^31-1)^4`. The difference from
`2^-100` is a local screen for the unsupported moment. It is not an available
global budget: other source/recovery/payment/FS terms are unresolved, and
`farWrong` is not the final knowledge experiment. The machine-readable global
bound and remaining global allowance are both null.

Image, ordinary-row and first-round events overlap with the moment and with
other restricted theorems. The historical 396430 inventory is not imported.
No relation repair is credited twice. Hiding and the resource-bounded
Fiat-Shamir theorem retain their separate obligations, including adaptive
views, nonces, prequeries, retries, restorations and extractor running time.

The unchanged maximum body is

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

This continuation adds no verifier messages or operations. It supplies no new
complete-transaction CU, prover runtime, or actual extractor runtime result.
The Rust search timings are host measurements of the reduced strategy search.
All focused proof commands, source/olean hashes, exits, wall times, RSS, swaps
and standard-only axiom audits are collected in
[rational-continuation-evidence.json](rational-continuation-evidence.json).

The two newly resumed laptop checks passed on their first attempts:

| Target | Exit | Wall | Peak RSS | Swap |
|---|---:|---:|---:|---:|
| `SevenAlphaRecovery` | 0 | 49.27 s | 4,799,414,272 B | 0 |
| `ThreeTauRecovery` | 0 | 49.07 s | 5,281,333,248 B | 0 |

Both use only standard Lean axioms, with no `sorry` or new axioms. Their
source and cached imported closure were checked before and after each run.
See [seven-alpha evidence](seven-alpha-recovery-review.md) and
[three-tau evidence](three-tau-recovery-review.md) for exact commands and hashes.

Recheck recorded evidence without rebuilding:

```sh
python3 -B docs/research/v8-no-work-100-20260907/experiments/audit_rational_continuation.py --check-recorded
```

This audit passed for all 16 listed leaves, including 116 standard-only
declaration audits, and the recorded exact rationals match the Python integer
calculations. The new runners passed `bash -n`. The unrestricted Git whitespace
check reports whitespace emitted by archived failed Lean diagnostics and final
blank lines in frozen, hash-pinned sources/runners. Those bytes are preserved
as executed. The source/document check passes with logs excluded and only
`blank-at-eof` disabled; no proof or script was reformatted after its recorded
execution.

Individual `run_*.sh` commands are recorded in each linked report. They refuse
to overwrite an existing log. Replays are restricted to changed leaves with
cached dependencies and the existing memory guards. The NUC thermal pause was
respected; resumed focused Lean work is on the laptop.

The decisive next experiment is a bounded collector for common-support forks:
log the actual frozen prefixes, authenticated values, adaptive finals and
failure reasons, and test whether it constructs the certificate just proved.
The accepted mass that it cannot turn into a certificate or another valid
witness still needs a quantitative theorem. Four-kappa and gamma/component
composition also remain. The current grammar remains a candidate; a global 100-bit argument,
source/FS theorem and full-view privacy proof are not complete.
