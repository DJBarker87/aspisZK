# Sparse reconstruction constraints and a concrete relation transpose

Continuation of [chord-verdict.md](chord-verdict.md). Source base
7457598e4712fb0b4bd1c5d6770e875a38f75bd1; same pinned field and tensor conventions.
Only this research directory changed. The user additionally requested the branch
be committed and accessible; publishing this research branch is separate from
merging, deployment, or changing production.

## New algebraic result

Write the selected natural tensor as q[2j]=A_j, q[2j+1]=B_j in
phi_j(x)=product of T_(2^k)(x) over set bits k of j. This is the actual
y-low-bit circle tensor convention, not the monomial coordinates used in the
previous division experiment. For L=a+bx+cy, reconstruction is

    A_f = a A + b x A + c (1-x²) B + I_A
    B_f = c A + a B + b x B + I_B.

Multiplication by x has a sparse binary-carry representation because
T_m(x)^2=(1+T_(2m)(x))/2. Each carry through a set bit contributes a constant
branch with half the incoming coefficient and propagates the other half upward.
All terminating branches have smaller indices; the final branch raises the
first unset bit. This proves the sparse operator used in `chord_link.rs`.

Let d=2^-9 in M31. The only possibly nonzero reconstructed coefficients beyond
the original 1024-dimensional space are

    f[1024] = d * (b*q[1022] - c*q[1021])
    f[1025] = d * b*q[1023]
    f[1026] = -d * c*q[1023]
    f[1027] = 0.

Higher entries are structurally zero by the degree bound. Since a genuine
chord has (b,c)!=(0,0), reconstruction lies in the original space **if and only if**

    q[1023] = 0,
    b*q[1022] - c*q[1021] = 0.

Thus the two membership conditions really are sparse in the selected basis.
The prior Laurent-space constraint is not an expensive change of basis that
the verifier must compute. The affine interpolant has only entries 0 and 1
(y case) or 0 and 2 (x case), so it does not change the overflow conditions.
This is a mathematical derivation plus exact tests, not a machine-checked theorem.

## Relation transformation

Let P discard the overflow entries and M denote multiplication by L in the
extended tensor basis. An original functional w satisfies

    <w,f> - <w,I> = <M^T P^T w,q>

once membership is established. This statement is an exact linear identity.
The prototype implements forward M and its transpose independently and tests
the identity for every input basis vector. It also verifies reconstructed
polynomial evaluations at a non-chord probe and the affine correction.

For X = multiplication by x on line tensors, the transpose weights are

    w'_A = a*w_A + b*X^T*w_A + c*w_B
    w'_B = c*(w_A-(X²)^T*w_A) + a*w_B + b*X^T*w_B.

The same formula supports overflow test functionals when w is extended rather
than zero-padded. It gives a constructive bridge for linear claims, not yet
the production `WeightAccumulator` representation or a verifier implementation.

## Proof bytes and security accounting

Two known-zero claims need no transmitted claim values. An exploratory relation
batch can include E1=q[1023] and E2=b*q[1022]-c*q[1021] as
S + eta*E1 + eta²*E2. Sampling eta from the existing field adds transcript work
but no proof-body field. The membership part touches only three coefficients.
For a fixed nonzero residual triple, uniform eta gives at most 2/|K| error.

**This is only a fixed-object statement.** A decoded q can depend on later
challenges, even though the committed leaf oracle was fixed earlier. The actual
restored-execution reduction must establish the relevant residual's conditioning
and selection law. It cannot insert 2/|K| into the full ledger without that step.
Eta also changes transcript labels, oracle counts and source binding; it is not
a free compiler operation. Reusing an existing challenge without a fresh
conditioning argument is not justified.

No additional proof bytes are algebraically necessary for these two constraints
and the transposed linear claim alone. Consequently this experiment does not
force the modeled body above the user-accepted 40,282 bytes. It does **not**
establish a complete byte census: adaptive hiding, extraction and any replacement
structured weight representation remain unimplemented.

## Executed optimized prototype and cost

From the worktree root:

```sh
rustc --edition=2021 -O docs/research/v8-no-work-100-20260907/experiments/chord_link.rs -o /tmp/aspis-v8-chord-link
/usr/bin/time -l /tmp/aspis-v8-chord-link
```

Final changed-source run: exit 0, 0.86 s wall, 0.50 s user, maximum RSS
1,982,464 bytes, zero swaps, zero block input/output operations. Apple M3,
macOS Darwin 25.5.0 arm64, Rust 1.93.0. Compilation excluded from timing.

- 2,048 exact natural-tensor basis forward/transpose checks (two legal chords,
  including equal-x/opposite-y).
- 1,026 independent evaluations of the x-carry identity.
- All 2,048 basis cases check the four explicit overflow formulas.
- Invalid top basis inputs detected; interior image and affine correction checked.
- Full-vector transpose: 3,072 QM31 products and 3,070 mixed M31 products,
  excluding allocation/indexing/addition costs. This is a concrete operation
  count, not an optimized lower bound or CU measurement.
- 200 host calls, allocations included: mean 69,753 ns, p50 69,625 ns,
  p95 69,917 ns, maximum 84,209 ns. These are warm synthetic microbenchmarks,
  not prover time or full-transaction benchmarks.

Earlier run only checked generic reconstruction; subsequent runs changed the
probe to avoid a chord root and added sparse overflow checks. No unchanged
large regression or package build ran. No Lean/SBF/full prover execution.

## Updated decision

Reverse membership and linear relation transport now have **explicit algebraic
constructions and full-dimension finite tests**. That is stronger than the
previous statement of missing obligations. They are not currently connected to
the source verifier or proved adaptive-sound.

The expensive-looking part is not membership but terminal evaluation of the
transformed relation weights. The full-vector reference is suitable for a
prover/control experiment, not evidence of CU parity. A promising bounded next
engineering test is to apply the carry identity directly to the existing
structured tensor/grouped-mask weight components, computing terminal values
without materializing all 1024 weights. A favorable result still needs the
coherent-extraction existence theorem and full-view hiding analysis before SBF.

The principal security decision remains unchanged: the 28-root uniqueness
argument does not construct coherent extractions from accepted arbitrary
oracles. No 100-bit or unchanged-CU claim follows from these new identities.

## Further structured calculation (subsequent changed-source run)

`chord_link.rs` now evaluates `<w,Mv>` directly when w and v are rank-one
bit tensors. For line tensor factors define d_k=w[k,0]v[k,0]+w[k,1]v[k,1].
The carry identity gives `<w,Xv>` as a sum of nine prefix/suffix products,
without materializing a vector. Also X²=(1+T2)/2, so its contraction is half
the identity contraction plus half a carry starting at the second line bit.
Combining these contractions with the y-bit factors implements `<w,Mv>` in
O(log dimension) field operations. It uses no inverses and permits zero factors.

All 32 synthetic tensor cases (including zero factors) matched the independent
full forward map. Updated optimized run: exit 0, 0.90 s wall, 0.51 s user,
2,064,384 bytes maximum RSS, zero swaps. Two hundred warm scalar calls:
mean 1751 ns, p50 1750 ns, p95 1792 ns, max 1917 ns. The same run's full-vector
transpose mean was 69721 ns; the outputs differ, so this is not a full-verifier
speedup comparison. Prior 2048 basis/overflow checks also passed unchanged as
part of this changed-source executable.

**Source limitation caught during inspection:** the selected relation covector
fold uses `[1,alpha³,alpha²,alpha]/4`, which is generally not a rank-one two-bit
tensor (its unscaled 2x2 determinant is alpha-alpha^5). Thus the new scalar
kernel must not be substituted once per terminal component as if every actual
fold covector were rank one. A correct implementation needs two-bit block
contractions or an explicitly charged sum of product tensors. Grouped inactive
masks also are not generally single product tensors. These missing adaptations
and source bridges prevent converting the microbenchmark into CU parity.

The security shortcut is now explicitly refuted in
[recovery-counterexample.md](recovery-counterexample.md). The structured
calculation does not resolve that independent cryptographic problem.

Subsequent ZIP review resolves the actual two-bit-block limitation for Product
components: [zip-review.md](zip-review.md). `block_terminal` now implements all
four real dual folds, and 40 cross-language cases agree on all terminal values.
Its count is 91 generic products including the outer scale. Grouped-mask handling,
source factor-order adaptation and full CU measurements remain outstanding.
