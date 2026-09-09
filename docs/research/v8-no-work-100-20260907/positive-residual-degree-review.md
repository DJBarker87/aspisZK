# Positive-transfer addition: individual degree and unchanged round width

Pinned research revision: `d5507a8f247bbed7cd35591c240d8d7a40af67a0`.
This is a focused continuation of the proved terminal insertion, not a new
verifier design or a global soundness claim. No Rust, proof-body, production
or deployment changes are made here.

## Result and exact meaning

`PositiveResidualDegree.positive_delta_degree` proves that the added
positive-transfer term has degree at most **14 in any one varying sumcheck
coordinate**, with all other coordinates fixed arbitrarily. The component
tables are arbitrary fixed field-valued tables, not assumed honest,
recoverable, zero-residual or equal to a known witness. The finite sum over
remaining Boolean assignments also has degree at most14. Adding it to an
existing degree-at-most27 restriction therefore still fits the existing
degree27 / 28-coefficient semantic grammar.

The final v4 leaf is **kernel-checked**, including the explicit
last-coordinate optimization identity from `v6_statement_points` below.
All twelve audited declarations use only standard Lean axioms.

This closes the added-term degree obligation recorded in
[the positive-transfer report](positive-transfer-review.md). It does
**not** reprove the old terminal's degree, assume that any 28 sampled values
automatically represent the intended polynomial, or establish that an
accepting proof enforces every semantic constraint.

## Actual source path

| Source at the pin | Precise role in this restriction |
|---|---|
| `experiments/payment_extraction.rs:26–27,43–45` | `point_rows` calls `v6_statement_points`, then evaluates every fixed message column using `multilinear_evaluate_qm31`; `terminal` selects the 84 claims from those same rows |
| `aspis-core/src/v6_transcript.rs:529–545` | Actual selected point producer: row0 is z; row1 is polynomial successor; row2 complements coordinates7/6. Last successor coordinate is handled as `1-z[9]`, carry starts at `z[9]`, then the reverse loop applies `bit+carry-(bit*carry+bit*carry)` |
| `aspis-statement/src/constraints_v4.rs:601–627,782–792` | Big-endian Boolean selector products and sum against message cells. The sparse implementation omits only rows whose trailing Boolean factors are zero; the mathematical formula is the dense Boolean MLE sum |
| `aspis-core/src/state_only_prefix.rs:587–600`; `state_only_poseidon.rs:95–106` | Matching generic reverse-carry formulas. These corroborate the convention but are not substituted for the actually called V6 helper |
| `experiments/positive_transfer.rs:63–84` | Residual is `claims[1]*claims[29]*claims[3]-1`, multiplied by the row1014 selector, packed in tower slot2, theta27, eta and equality weight |
| `experiments/payment_extraction.rs:93–107` | Each semantic round fixes the prior challenge prefix, varies its next coordinate, and sums over **all** remaining Boolean assignments before interpolating the degree27 message |

The two amount occurrences are the **same actual C1 column1** evaluated at
z and successor(z). The degree theorem allows independent recipient/change
tables; setting both to that fixed column is a valid specialization. The
inverse occurrence is the MLE of fixed C1 column3. It is **not** an inverse
computed from off-domain amounts: replacing it with
`1/(r(z)*c(successor(z)))` would be a rational function and is not the source
or the theorem.

Before the semantic round, eta, theta, the equality point, committed tables
and tower basis are fixed. `PositiveTerminalInsertion.literalPack_slot2`
identifies packing `[0,0,w,0]` with multiplication by the fixed QM31 element
u. Thus all theta/eta/tower factors are one constant `scale` in the new
univariate polynomial; they consume no variable degree. This uses the
previous concrete packing theorem, not a new unverified packing premise.

## The new mathematical argument

For coordinate j, `varyingPoint` places X at j and a constant polynomial at
each other coordinate. A finite product of **distinct** coordinate factors
has degree at most1: only one factor can vary. The proof bounds the sum of
individual degrees by the single supported indicator, without enumerating
the field or expanding a 1,024-entry tensor.

For source successor coordinate i, the incoming carry is

```text
carry_i = product of z_l over l > i.
```

The current bit is absent from that strict suffix. Therefore `z_i*carry_i`
also has degree at most1 along any one original coordinate. This is the
essential step: applying the generic product bound independently to the bit
and carry and charging degree2 would miss their disjoint variable support.
The full successor coordinate is a sum of these affine polynomials and is
therefore affine too. Each of the ten MLE factors evaluated at successor is
affine, giving degree at most10 for the composed MLE.

| Factor in the added term | Proved individual degree ceiling |
|---|---:|
| C1column1 MLE at z | 1 |
| C1column1 MLE at polynomial successor(z) | 10 |
| Fixed inverse-table MLE at z | 1 |
| Row1014 selector | 1 |
| Equality with fixed zerocheck point | 1 |
| Fixed eta/theta27/tower scale | 0 |
| Full addition, including subtraction of1 | **14** |

The selector is modeled by `Nat.testBit 1014 (9-i)`, exactly the big-endian
bit extraction in the wrapper. The equality coordinate is the literal
`1-a-z+a*z+a*z`; no honest Boolean-coordinate premise is used.

## Checked interfaces and remaining source boundary

| Declaration | What it establishes |
|---|---|
| `carry_source_initial`, `carry_source_update` | The suffix-product carry has initial value1 and obeys the actual backward-loop multiplication update |
| `successor_source_last` | The final empty-suffix step equals `1-z[last]`, exactly matching V6's optimized first iteration |
| `varying_eval`, `successor_eval` | Polynomial evaluation equals the specified one-coordinate input / source-shaped successor values |
| `mle_eval` | Polynomial sum/product evaluates to the Boolean MLE sum/product for arbitrary fixed table entries |
| `ordinary_mle_degree`, `successor_mle_degree` | The two distinct degree claims,1 and n; specialized to n=10 only at the final term |
| `row_selector_degree`, `equality_weight_degree` | Each public weight adds at most one degree |
| `positive_delta_degree` | Complete source-shaped additional restriction has degree≤14 |
| `remaining_assignment_sum_degree` | Summing the suffix assignments does not increase14; no sampled/favourable assignment replaces that sum |
| `existing_degree27_grammar_preserved` | Existing degree≤27 plus the new≤14 term remains≤27 |

These are kernel-checked algebraic/source-shaped statements, not an Aeneas
translation of the Rust loops, array parser or sparse trailing-Boolean
optimization. The source inspection identifies their formulas and fixing
boundaries. The exact memory/index-to-Boolean-function representation and
sparse evaluator refinement remain part of the larger Rust/source bridge;
they are not replaced by a `sourceMatches` premise in these proofs. No old
degree theorem was imported to assert the new successor bound. The older
V5 six-plus-one MLE factor and accepted degree27-message lemmas address
different obligations, so reusing their numerical conclusions here would
not prove this added term's degree.

## Evidence and reproduction

Focused cached Lean only, on the shared development machine under a serialized
7-GiB process-tree RSS guard and `lean -M7000`; no new dependency export or
package-wide replay. The runner pins source against d5507a8f, checks the
cached mathlib commit/olean, and records source hash, exact command, Lean
version, exit, wall time, RSS, swap and axiom output.

| Attempt | Exit | Wall | Peak RSS | Swap | Evidence |
|---|---:|---:|---:|---:|---|
| v1, local notation/helper/evaluation errors | 1 | 18.43 s | 5,513,494,528 B | 0 | [v1](experiments/positive-residual-degree-v1.log) |
| v2, complete degree14 endpoint | 0 | 9.27 s | 6,331,645,952 B | 0 | [v2](experiments/positive-residual-degree-v2.log) |
| v3, new last-coordinate lemma with stale library name | 1 | 14.99 s | 6,195,691,520 B | 0 | [v3](experiments/positive-residual-degree-v3.log) |
| v4, exact last-coordinate branch and complete final leaf | 0 | 7.13 s | 6,321,307,648 B | 0 | [v4](experiments/positive-residual-degree-v4.log) |

The first attempt's max-recursion error at the final goal was removed by
explicitly unfolding only the outer `delta` definition, not by expanding
its MLE sums or raising any resource limit. Other fixes were explicit
indicator parentheses, finite-set simplification and a generic Boolean
factor evaluation lemma. The last-coordinate addition initially used a
finite-set lemma name absent from the pinned library; the final proof uses
direct finite-set extensionality and the symbolic maximal-index bound.
No memory-pressure retry, increased cap or concrete-field enumeration was
used. The final v4 axiom audit contains only
`propext`, `Classical.choice`, `Quot.sound`; failed-log `sorryAx` output is
not retained theorem evidence.

Final source SHA-256:
`81a0da0915c77a0c335becb78db2eccd5346db240fabbb42900c55c0d50c566c`.
Exported olean:
`ce720f613b394c7993213539ed7c258d6edfe9b972ebaba0fa978ae48e9e7a01`.
The source and runner are frozen after this check; `git diff --check` and
runner syntax checks pass. Only Mathlib is imported by this new leaf, from
the pinned cached package; it does not consume concurrent main-worktree
source or an unverified new olean.

From the research worktree, with a fresh log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_positive_residual_degree.sh docs/research/v8-no-work-100-20260907/experiments/positive-residual-degree-recheck.log
```

No proof generation, SBF run or transaction-CU measurement was performed.
The 40,282-byte maximum is unchanged. Degree compatibility alone neither
certifies the new mask distribution nor discharges adaptive recovery,
semantic batching, authentication, extraction resources or Fiat–Shamir.
