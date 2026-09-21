# Verification performed in this review environment

Date: 21 September 2026. Source base: 6677d5f1310ff7373301fbd79f186278f772e68a.

## Executed and asserted

| Exact modeled check | Configurations | Result |
|---|---:|---|
| Sparse G / current T, M31 parameters | 16 | rank601 of624 |
| Sparse G / current T, full QM31 parameters | 6 | rank601 of624 |
| H1 / current T, M31 | 8 | rank540 of562 |
| Negative first271 CODE-coordinate placement, current T | 4 | rank538 of624, below601 |
| Negative bit-affine T / H1 | 8 | rank517 of562, below540 |
| Minimum-support T / H1, M31 | 8 | rank540 of562 |
| Minimum-support T / sparse G, M31 | 8 | rank601 of624 |
| Minimum-support T / H1, QM31 | 2 | rank540 of562 |
| Minimum-support T / sparse G, QM31 | 3 | rank601 of624 |

Total: 63 finite rank configurations. Each probe also checks1024 inverse
basis cases and89 legal balanced unit images for its chosen transform.
Those repeated structural checks are NOT counted as additional independent
probability samples.

Operator checks compiled with full QM31 arithmetic:
-295 sparse-terminal cases:24 generic/degenerate parameter choices plus all
 271 selected input basis positions. Each compares grouped and nested-carry
 forms with an independently applied full natural-chord adjoint reference.
-32 full legal-coordinate split/join and dual-functional identities, retaining
 752 complementary coins.
-16 minimum-support transform contractions against the complete dense dual
 reference for arbitrary weights; support163 verified.
-32 arbitrary-vector two-channel sharing identities.
-32768 tensor entry comparisons for the REJECTED bit-affine map. These show
 why a fast correct tensor implementation is not itself a privacy argument.

The runner compiles C++17 with -O3 -Wall -Wextra -Werror, WITHOUT -DNDEBUG.
The source explicitly rejects NDEBUG builds. Successful exact JSON records
are included. Field arithmetic is a separately written reference over
M31, CM31[i^2=-1], QM31[u^2=2+i], not the production Rust implementation.

## Scope limitations

Raw points are constructed from explicit rational parameters. They are not
replayed source q22 draws or guaranteed members of the actual source subgroup.
The tests assert distinct line roots, nonzero x/y, and nonzero raw chord
values. OOD and semantic/fold parameters use deterministic finite families;
no random-oracle distribution or probability bound is inferred from them.

The rank code constructs a source-shaped 624-by1022 G map and562-by1022 H1
map. Its arithmetic and ordering were inspected against pinned source, but
no automatic extraction or proof of Rust equivalence occurred. Full-rank
homogeneous maps do not establish the actual opposite-witness affine target,
public quotient, or causal full-view simulator. Those source tasks are explicit
in CODEX_TASK.md. The first271 negative here is in CODE coordinates; do not
mislabel it as the repository's original-row First271 test with618 rows.

No Rust compiler, Cargo, Lean, SBF toolchain or SVM execution was available
for these new files. Rust files are uncompiled integration drafts. No under-
budget cost, on-chain success, privacy or soundness theorem is claimed.

## Development failures and replay

An early experimental build had NDEBUG; its assertion-based outputs were not
accepted as verification. Final binaries were rebuilt with assertions and
all63 rank configurations and listed operator checks were completed on those
binaries. Later source guards make this mistake fail compilation.

A new operator test initially failed compilation because a local name
`changed` was used for two different types. The unused prior variable was
removed; no equation or expected output changed. Final build and checks pass.

The first all-in-one orchestration hit the container wall timeout after six
case groups. There was no continuing background process. The remaining four
groups were executed in a separate focused call using the same binaries,
then every recorded result was checked against its required value. This is
not reported as a successful uninterrupted first run.
