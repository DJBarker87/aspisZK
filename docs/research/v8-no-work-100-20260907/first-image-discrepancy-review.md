# First image discrepancy: source-shaped compact boundary

Research checkpoint: `15e73e9fdf529a0d0ab46353b98bccaf029bf4f5` on
`research/v8-no-work-100-20260907`; the worktree was initially clean.
This continuation adds only the deterministic field interface needed to
compose the first image/relation stage with the completed
[ordered post-query constructor](ordered-post-query-review.md).

## New endpoint

[`FirstImageDiscrepancy.lean`](experiments/FirstImageDiscrepancy.lean) defines
`Before` with fixed ordinary weights, the reference coefficient vector `Q`,
the ordinary scalar, quarter constant, and chord coefficients `b,c`. It has
no tau, response, alpha0, final or query field.

For this prefix it constructs

```
prior = claim - dot(ordinary,Q)
E1 = Q[1023]
E2 = b*Q[1022] - c*Q[1021]
errorPolynomial(tau) = prior - tau*E1 - tau^2*E2.
```

The `error_eval` theorem proves that this polynomial is **the actual
scalar-minus-dot discrepancy** after adding the image terms to the ordinary
functional while leaving the claim unchanged. It instantiates the existing
sparse `image_boundary` theorem at the three literal coefficient indices;
it does not materialize or normalize 1,024 symbolic cells.

`Before.firstError tau sent` is the actual claimed compact polynomial minus
the honest arity-four convolution for the image-augmented weights and `Q`.
The response consists of six arbitrary transmitted fields. The omitted
quartic is reconstructed by the already checked compact grammar. The new
interfaces derive:

| Declaration | Derived fact | Conditions |
|---|---|---|
| `error_eval` | The scalar image polynomial equals `claim-dot(imageWeight,Q)` | Arbitrary fixed ordinary weights/claim/reference vector |
| `error_degree`, `error_nonzero` | Degree at most two; nonzero whenever `E1 != 0` or `E2 != 0` | The existing `JointImageGame` image lemmas are reused, not re-proved |
| `firstError_degree` | Actual compact-response discrepancy has degree at most six | Arbitrary six-field response |
| `firstError_boundary` | Its relation boundary equals `errorPolynomial.eval tau` | `quarter*4=1`, needed for the actual omitted-quartic reconstruction |
| `firstError_nonzero` | A nonzero incoming image discrepancy makes that compact-error polynomial nonzero | Same quarter identity; no successful-response or acceptance premise |
| `snapshot_*` | Image weights, true final coefficients, carried scalar and true error coincide with the existing `PostQueryFunctional.Prefix` definitions | Literal structure construction |
| `firstError_eval` | Evaluation of the first error equals the actual carried scalar minus the folded reference dot | Existing V7-consumed convolution/dual-fold identity |

No boundary equality or terminal equality is supplied by the caller. The
quarter identity is a field-constant interface, not an assumption that a
prover residual vanishes. These lemmas do not assume the ordinary prior is
zero and do not restore `inactiveExact`.

## Causality and remaining interfaces

The intended caller has the shape

```
before : Before
firstResponse : K -> Sent K                    -- response0 depends on tau
snapshot tau (firstResponse tau) alpha0         -- alpha0 follows response0
final : K -> K -> (Fin 256 -> K)                -- may depend on tau, alpha0
```

Thus the first-error polynomial can be fixed after tau but before alpha0;
the final may then be adaptive. `snapshot` alone does not certify byte-level
ordering: it is a deterministic constructor, and an unconstrained caller
could still pass a response selected too late. The parent causal-game
construction must use the stated strategy type and fresh conditional law.

The reference `Q` is an analysis input, not data read by the byte verifier.
No theorem here makes an arbitrary received oracle polynomial or supplies
an anchor. The relationship between its image coefficients, the actual
component quotient, chord/interpolant, and authenticated openings remains
a separate source/recovery obligation. The ordinary vector is arbitrary
here: constructing it from the shifted kappa rows and compact functional
description is also not silently assumed completed.

The selected research transcript still binds its 545-byte public functional
description and unchanged scalar before tau. This leaf changes no transcript
bytes or challenge boundaries, and supplies no independent randomness or
Fiat–Shamir theorem. All prover nonce/retry/oracle-selection powers remain
visible in that later resource accounting.

## V7 reuse and evidence

This consumes `OptimizedRelationRefinement.discrepancy_degree`,
`discrepancy_boundary`, and `discrepancy_eval`, which already construct the
six-field grammar from V7-consumed generic `V6TranscriptRelationGrammar`,
`V5FriRelationCandidateBridge` and arity-four fold lemmas. It consumes the
existing sparse image interface and image degree/nonzero results. It does
not import a q16 sampler, grinding allowance, work multiplier, or historical
396430 aggregate inventory.

Reproduction from the research worktree, using a new log filename:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_first_image_discrepancy.sh \
  docs/research/v8-no-work-100-20260907/experiments/first-image-lean-v2.log
```

The runner resolves `lake env` before launching Lean itself, so no live Lake
parent or dependency build accompanies the focused leaf. It uses
`lean -M7000`, an independent 7-GiB aggregate descendant-RSS guard, and an
exclusive compile slot. It checks imported research source/olean hashes,
traverses the repository import closure, matches source in both worktrees
against the research checkpoint, and records unchanged source/olean
provenance before and after the run.

The read-only main worktree revision recorded during both runs was
`d851f36bc0ee41459156e125aaa04e4a0941ac70`; moving main itself is not treated
as cache provenance. Lean is 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`),
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.

| Evidence | Exit | Wall seconds | Peak RSS bytes | Swaps | Result |
|---|---:|---:|---:|---:|---|
| `experiments/first-image-lean-v1.log` | 1 | 15.14 | 5,504,139,264 | 0 | Missing namespace for `monomialPolynomial`; failed elaboration evidence only |
| `experiments/first-image-lean-v2.log` | 0 | 3.60 | 5,664,161,792 | 0 | All 12 requested audits use standard axioms only; imported provenance unchanged |

The final source has no `sorry` or new axioms. The allowed audited axioms
are subsets of `propext`, `Classical.choice`, `Quot.sound`. No resource limit
or recursion allowance was increased, and no unchanged earlier theorem was
replayed.

Final SHA-256 pins:

```
FirstImageDiscrepancy.lean
ef2d19ab25ae7b2d6795067b95b678253bed446004cb8541c0188893c69d7230
FirstImageDiscrepancy.olean
a6152344385cb7bfe633674d48c4217725ad07427c37eca6497706179567c1ab
run_first_image_discrepancy.sh
0ee2f2b74279147f867b678a64d319e821c26d568fc9ae7b63687e9d27f05f97
```

## Accounting

These are deterministic bridges, not newly independent security events.
The existing image-mix and first-repair terms must be charged once by the
causal composition, alongside its ordered post-query tail; this leaf does
not add a second copy or declare a global numerical bound.

No Rust, verifier, proof-body or production file was changed. The body
remains 40,282 bytes. No SBF/CU, proving latency, extraction runtime or
privacy measurement was performed. Full-view simulation, authentication,
actual source translation, arbitrary-oracle recovery and payment knowledge
remain separate gates. The immediate next consumer is the causal pre-tau
strategy composed with the constructed ordered noisy post-query game.
