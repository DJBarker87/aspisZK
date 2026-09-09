# Queried poles and the checked quotient residual

Status: both focused leaves are kernel-checked, with standard-only axiom
audits and unchanged pinned import provenance. Research source pin:
`113dc5dacbf630c234cc6498385913507c171f8f`.

## The interface being closed

The mathematical virtual word uses total field division. At a chord pole its
value is therefore zero. The actual verifier does not accept that replacement:
the queried denominator array is checked and a zero produces `Error::Domain`.
The intended adapter is **successful query calculation implies the mathematical
quotient/fold residual**, with queried poles rejected deterministically. It is
not a new small pole probability or a global polynomiality assumption.

The source order is fixed:

1. The 22 query ordinals are sampled after final256; rho follows the query array.
2. Canonical gamma recombination produces four received values per ordinal.
   Authentication entries are sorted separately, without sorting query values.
3. Slot order is `(x,y),(x,-y),(-x,-y),(-x,y)`; denominator and numerator arrays
   use offset `4*ordinal+slot`. The denominator is `a+b*x+c*y` and numerator is
   `received-(intercept+slope*selected_coordinate)`.
4. The retained optimized path computes CM31 line norms, then their M31 norms.
   The joined batch shares a base inverse between those norms and the independent
   `[2*x,2*y]` fold-denominator array, whose offsets are `2*ordinal` and
   `2*ordinal+1`. Two conjugate-and-scale steps reconstruct each QM31 inverse.
5. The fused normalized fold consumes those quotient values and fold inverses.
   The game residual is **final evaluation minus received fold**. Plus updates
   to the relation scalar and weights consequently preserve the existing
   degree-q shifted-rho discrepancy, not an unshifted/q−1 substitute.

## Proved scope and reused V7 work

| Interface | New artifact / reused result | Scope |
|---|---|---|
| Exact nested QM31/CM31 norm, inverse reconstruction and zero test | `QueriedInverse`; retained exact QM31 tower | Field-coordinate algebra; all values, not honest values only |
| Checked prefix/backward batch | `JoinedInverse.checked_correct`, `shared_product_seeds`, `joined_eq_separate` | Reuses the established checked algorithm and shared seeds; no reciprocal assumption |
| Optimized five-coefficient norm and shared line coordinate | `CircleNorm.four_slots`, `LineNorm.four_line`; new `lineFour_norms` | Requires the same unit point and derived `2*x²−1`; no unchecked coordinate hint |
| Source child slot signs | `V7ExactOneFoldDomains.storedInitialCirclePoint20_{x,y}_slots` | Actual stored log20 order, reused unchanged |
| Sparse interpolant numerator | `OODInterpolant.vector_eval`, actual x/y branch | Does not require correct OOD answers, image validity or received polynomiality |
| Returned denominator/fold inverse buffers | `QueriedResidual` | Both output buffers, not ideal inverses substituted for source outputs |
| Fused normalized fold | `QuotientFold.fold_identity`, V7-consumed concrete circle butterfly | Preserves the minus-y second pair and all challenge values |
| Totalized oracle residual and ordered rho injection | `SelectedReceivedOracle`, `PostQueryFunctional` | Adapter preserves ordinal order and final-minus-received sign |

The concrete new endpoints are:

- `QueriedInverse.checked_spec`: the checked nested-norm model returns exactly
  the inverse lists, or rejects its empty/zero-input cases. `normK`, `normC`
  and both conjugate reconstruction steps are literal tower coordinates.
- `QueriedResidual.queried_pole_fibre_reject`: if any query names a fibre in
  the existing `poleFibres d`, the checked inverse path returns `none`.
- `QueriedResidual.success_slots`: for arbitrary fixed received data, success
  yields exactly `virtual d received (childIndex query slot)` at every queried
  slot, including the true sparse-interpolant subtraction.
- `QueriedResidual.success_base_inverse`: the returned base-inverse buffer
  supplies the actual `1/(2*x)` and `1/(2*y)` fold inputs. These values are not
  substituted as ideal inverses in the source-fold definition.
- `QueriedResidual.success_fold` and `success_residual`: the fused arithmetic
  gives exactly the SAME selected-domain oracle fold, and the residual equals
  the existing ordered compact game's final-minus-fold residual.

No image validity, correct OOD claims, anchor membership, received polynomiality,
or separately asserted reciprocal-product equality is a premise. The parser/
authentication boundary supplies field values as explained below. The analysis
reference is zero in the oracle constructor because the source fold is reference-
independent; this does not assert that the received word is the zero polynomial.

This does not translate the Rust byte parser, packed gamma arithmetic, hash
authentication, immutable selected-point wrapper, or Vec memory/index operations.
The checked model uses `JoinedInverse.separate`; the retained joined-specification
and shared-seed lemmas justify the corresponding mathematical outputs, but the
actual single-inverse Vec loop is not newly translated here. `lineFour_norms`
is likewise a separate component identity, not a complete optimized-buffer
constructor theorem.
The line-norm coefficient identity and nested inverse model must still be joined
to those actual source paths by translation/refinement or separately delimited
source evidence. In particular, an independently supplied norm/line array is not
an accepted input to this interface.

The canonical source decoder checks all 104 C1 limbs and 48 C2 limbs, rejecting
the 31-bit all-ones encoding `p`; C1 uses `26*slot+column`, while C2 uses
`4*(4*helper+slot)+limb`. This is source inspection, not a new parser theorem.

## Security, cost and remaining work

Queried poles do not need a probability allowance: a successful checked query
path cannot contain them. Unqueried poles remain part of the mathematical word
and the already proved at-most-two pole-fibre reconstruction bound. No callback
or protocol source is changed by this work.

The proof-body model remains `697*16+52+24+22*621+2*296*26 = 40,282` bytes.
This continuation does not measure CU, proving time or extraction time, and
does not alter full-view ZK or Fiat–Shamir status. It supplies a deterministic
adapter for the successful arithmetic path, not a full acceptance-to-payment
extraction theorem. Far-regime recovery, early C1 source coupling and resource-
bounded extraction remain separate obligations in the parent continuation.

In a later source composition, the implication must be used **on the same
accepted execution**, before comparing it with the unconditioned ideal game.
Do not condition the query law on successful inversion and then reuse an
unconditioned uniform-query probability. The source rejects queried poles; it
does not resample queries to avoid them.

## Reproduction and evidence

Commands from the research worktree (fresh log names are required by the runner):

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_queried_boundary.sh QueriedInverse docs/research/v8-no-work-100-20260907/experiments/queried-inverse-v2.log
bash docs/research/v8-no-work-100-20260907/experiments/run_queried_boundary.sh QueriedResidual docs/research/v8-no-work-100-20260907/experiments/queried-residual-v2.log
```

The runner resolves the cached Lake environment and invokes the single changed
leaf with Lean 4.32.0, `-M7000`, `/usr/bin/time -l`, and an independent 7-GiB
aggregate process-tree guard. No package build or unchanged export was run.
Borrowed formal sources are checked against
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, not whichever concurrent main HEAD
happens to exist. Mathlib is pinned to
`81a5d257c8e410db227a6665ed08f64fea08e997`; sources and oleans are hashed before
and after the focused check. The new inverse dependency has its own pinned
source/olean pair in `experiments/queried-inverse-pinned.sha256`.

| Leaf / final log | Exit | Lean wall time | Peak RSS | Swaps | Axiom audit |
|---|---:|---:|---:|---:|---|
| `QueriedInverse`, `queried-inverse-v2.log` | 0 | 14.00 s | 5,607,866,368 B | 0 | Six declarations; standard axioms only |
| `QueriedResidual`, `queried-residual-v2.log` | 0 | 20.76 s | 5,739,167,744 B | 0 | Eleven declarations; standard axioms only |

Retained v1 failures were local proof/elaboration errors, not falsified
mathematics: inverse let reduction and ambiguous line-half theorem arguments;
then a missing index namespace, finite-vector simplification and a final-eval
definitional reduction. The latter was replaced by the already proved symbolic
`final_evaluation` interface. No memory/recursion cap was raised and no failed
proof is relied upon. Successful logs include harmless tactic/simp diagnostics;
all retained theorem audits exclude `sorryAx` and new axioms.

See [machine-readable evidence](queried-pole-evidence.json) for complete new
artifact pins, source pins, measurement scope and explicit remaining interfaces.
The next narrowly scoped source step is to package the actual immutable selected
points, derived line buffer, canonical gamma outputs and joined norm Vec loops
as this checked input/output interface. This is deterministic source work, not
another probability bound or a reason to alter the protocol.
