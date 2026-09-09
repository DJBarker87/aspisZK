# Constructed line/norm buffers and shared inversion

Research base: `1b8f72d9de123b16eb831754e58518e66a33d3f3`, branch
`research/v8-no-work-100-20260907`. The worktree was clean at inspection;
subsequent concurrent research files and main work were not changed.

This follows [the queried-pole adapter](queried-pole-review.md). That adapter
proved the correct query residual from a checked inverse model, but deliberately
left the optimized buffer constructor and single-inverse implementation separate.
This continuation targets those field/list interfaces. It does not add a
probability term or change the verifier protocol.

## Source and proved endpoint

The unchanged source files are `circle_norm.rs`, `line_norm.rs`,
`joined_inverse.rs` and their sole non-test caller in `relation_callback.rs`.
The fixed chord coefficients and immutable selected unit-circle points determine
all buffers; no norm, line coordinate or inverse is a prover-supplied hint.

1. Construct the actual five line-norm coefficients. The CM31 half operation is
   represented by the literal low31 word rotation on both canonical coordinates,
   not assumed equal to division by two.
2. Construct `t=2*x²−1` in the same order as the points. Zip that derived line
   list with the points, and emit the four norms in `(++,+−,−−,−+)` slot order.
3. Prove the resulting CM31 list is exactly `map normK denominators`, and its
   M31 image exactly `map scalarNorm denominators`; lengths are `4*n`, `4*n`,
   `2*n` and `n` for values, norms, base fold denominators and lines.
4. Run one shared inverse on the two M31 products, then the two reverse passes.
   Reconstruct each QM31 inverse using its actually computed CM31 norm.
5. Prove equality with `QueriedInverse.checked` on those constructed values/base
   inputs, including empty/zero rejection, without supplied buffer equalities.

The retained V7-consumed exact tower, earlier `lineFour_norms`, and checked batch
lemmas supply the algebra. They are reused without unchanged replays.

## Scope

`SharedInverseReplay` is kernel-checked: its explicit terminal seed is threaded
through the forward-prefix/reverse-return recursion. `finish` stores slot zero
from the final cursor without adding a nonexistent source operation. The single
inverse `(product_x*product_y)^-1` supplies both seeds, and the modeled output is
equal to the existing checked separate/joined specifications.

`LineNormBuffer` is now kernel-checked. Its endpoint is the unconditional
field/list equality

```text
inverseLines a b c points
  = QueriedInverse.checked (values a b c points) (base points).
```

`point_norms` derives the quartet from the five prepared coefficients and the
circle equation. `norms_eq` proves the same statement for the entire ordered
point/line traversal. `scalar_norms_eq` then supplies the exact M31 input to the
shared inversion. Reconstruction consumes the computed CM31 norm paired with
each denominator, rather than replacing that input by an assumed correct norm.
The equality includes the modeled empty/zero rejection branches.

The security implication is deterministic: within these field/list interfaces,
the optimization does not change which inverses the query check consumes or
turn a zero denominator into a valid reciprocal. It closes the buffer/algorithm
premises of the earlier checked-inverse model, not acceptance-to-extraction.

The input point type carries the actual unit-circle equation over M31. It allows
all unit points, not only those with nonzero coordinates. Zero fold denominators
still reach the checked rejection branch. Instantiation from the actual selected
point lookup and flattening its buffers into the existing queried-residual API
remain distinct from a translated Rust-machine execution.

The constructed buffers prove their own length relationships. The source also
checks `points.len()<=22` and independently supplied array lengths; this model
does not reproduce its error enum for over-cap calls or inconsistent arrays.
Its application is the actual q22 caller's internally constructed buffers.
This field/list development does not translate memory allocation,
Vec bounds, packed canonical gamma decoding or Merkle authentication. It also
does not claim a new CU saving from replacing the modeled recursion by source
loops; the implementation already performs this optimization.

## Budget and evidence

No production, transcript, proof, mask or runtime code was edited. The body
remains 40,282 bytes. No new verifier/prover/CU benchmark is part of this task,
and full-view ZK, actual Fiat–Shamir and payment extraction claims are unchanged.

Builds are serialized, focused, cached, capped with `-M7000` and an independent
7-GiB aggregate process-tree RSS guard. Borrowed formal source is pinned to
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, Mathlib to
`81a5d257c8e410db227a6665ed08f64fea08e997`, and Lean to 4.32.0.
The runner checks imported source/olean hashes before and after each build.
New dependency pins are recorded separately, never borrowed from unverified
concurrent source.

| Focused leaf | Exit | Lean wall time | Peak RSS, bytes | Swaps | Axiom audit |
|---|---:|---:|---:|---:|---|
| `SharedInverseReplay` v1 | 0 | 11.92 s | 2,859,483,136 | 0 | Four declarations, standard only |
| `LineNormBuffer` v3 | 0 | 16.08 s | 5,606,490,112 | 0 | Seven declarations, standard only |

The standard axioms are `propext`, `Classical.choice`, and `Quot.sound`; no new
axioms or `sorry` remain in either leaf. Source/cache provenance was unchanged
across both successful builds. These are compilation measurements, not prover,
extractor, verifier or SBF measurements. The observed cache worktree HEAD was
`e674314c6d062377f29df84f3c4c94d4ebd7572d`, while each borrowed source in the
import closure was checked against the older declared pin rather than trusting
that moving HEAD.

Failed v1/v2 logs are retained. v1 had local cast, finite-vector simplification,
and list-expression elaboration errors. v2 reduced this to the representation
of the literal two in the base field. The replacement uses the small exact
check `(2 : M31Exact) != 0`; it does not enumerate the field or normalize a
large recurrence. No memory cap was raised. Failed logs are not claimed proof
evidence even where Lean printed provisional declarations.

Reproduce in this research worktree with fresh log names; the runner refuses to
overwrite existing logs:

```sh
EX=docs/research/v8-no-work-100-20260907/experiments
bash "$EX/run_norm_buffer.sh" SharedInverseReplay "$EX/shared-inverse-replay-recheck.log"
bash "$EX/run_norm_buffer.sh" LineNormBuffer "$EX/line-norm-buffer-recheck.log"
```

The new dependency's checked source/olean hashes are in
[`shared-inverse-pinned.sha256`](experiments/shared-inverse-pinned.sha256).
Exact source, log and output hashes, successful and failed measurements, and
the unchanged budget are recorded in
[`line-norm-buffer-evidence.json`](line-norm-buffer-evidence.json).

The next source obligation after this constructor is the actual typed selected-
point/canonical-parser/Vec execution coupling; no root-count lemma or new
conditioning argument is needed for this deterministic interface.
