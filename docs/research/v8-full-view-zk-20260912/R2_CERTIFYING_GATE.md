# R2 certifying affine gate

Date: 2026-09-13.

`crates/aspis-prover/src/v8_privacy_affine_gate.rs` implements exact M31
elimination for a fixed affine observation map. It returns either a correction
matrix `C` checked by direct multiplication as `M*C=T`, or a functional
`lambda` checked to satisfy `lambda*M=0` and to detect one target column.
Malformed shapes, inconsistent certificates and workspaces above 2,000,000
field entries fail closed.

`certify_joint_affine` stacks earlier and later observations using the same
coin columns. Its regression demonstrates both the one-coin marginal/joint
trap and the sign error caused by replacing a real earlier witness offset with
zero. Rank deficiency is allowed when the legal target remains in the image.

## Source-linked scope

The current source adapter instantiates only the raw C1 opening block, using
the actual `CircleEncoder`, pair-forest relation-free mask cells, active-row
set, row-1023 balancing and the removed column-3/row-1014 draw. It reproduces:

- the column-zero row-913 `{4,6}` separator;
- the distinct column-three row-1014 `{1,2}` separator;
- all 768 predeclared same-four-fibre row-913 separators;
- the scattered 22-query schedule containing `{4,6}`, at rank 86;
- all sixteen raw columns at rank 88 for the fixed spread schedule.

The spread-schedule PASS is deliberately `RAW_C1_PASS`. It cannot issue a
publication permit and is not evidence that the complete view passes.

## Exact remaining coverage obstruction

R1 identified conditionally linear point, OOD, opening and fold maps, but the
selected generated q22 source does not expose one authenticated adapter that
constructs their rows with the same global mask columns. More importantly,
H1/C2 construction, semantic sumcheck messages and relation sumchecks remain
nonlinear or unsupported conditional blocks. No universal same-public offset
generator spans those blocks. Therefore a complete `[A;B]` and
`[T_old;T_new]` cannot currently be constructed without assuming precisely
the missing joint-view theorem.

R2 is complete for the supported raw affine block and blocked for full-view
authorization. The next smallest mathematical experiment is to source-adapt
the first nonlinear chronological block (H1/C2 before its root) and either
give a causal coupling or exhibit a same-public separating event after
conditioning on the C1 root. Until then the only sound adapter result is
`UnsupportedFullView`; reject-all containment is not a useful repair.
