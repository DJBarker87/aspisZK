# D272 candidate sibling

Recommended recipe pending owner approval; toolchain rustc 1.94.1 unpinned.

The branch is a candidate sibling. Candidate source is
`237e13556180d2ce0320a2760f89b35b5f4f02bb`; source inputs in this branch match it
except the standalone lockfile repaired by `1f02f0ecd7`.
The previous `dual/B` archive and its failed recipe remain historical evidence.
This artifact enables CT host prover, unlike both the original A and failed B.
No claim that this is shipped or that its source matches A is made.

The minimal offline workspace update ran in a separate task-owned source copy.
`lock/receipt.json` contains the complete three-line diff. It changes only
`aspis-r1-cert-build`, whose manifest gained the optional checker dependency.
All 423 registry entries compare equal as complete parsed package records
(including exact versions, sources, checksums and dependency lists).
No source under crates/, programs/, c3/ or tool source was changed.
No key or wallet was accessed or generated.

Native work uses sequential 6G/8G/swap0/Tasks64 scopes and the existing
reservation scanner and quiet-window shim. Lean is unnecessary for a binary
build/audit; 0/30 Lean and 0/0 Kani. No premise may be placed in T.

Build succeeded with exact requested feature syntax. Executable SHA256:
`898005412d46103cfeffe5740f7892ee01d1e3d73a7293338c62e679445b5e67`.
177.478 s build wall, 646,068 KiB GNU-time process peak RSS,
1,981,816,832 B cgroup peak, zero swap. The executable remains only on the host
at `bin/devnet_spend-B-recommended`; all task Cargo targets are removed.

`findings.json` covers N1–N8/R1/R4, `supplemental-findings.json` covers
R2/R3/R5/R6/R7. N1's scan prefix branches are removed; N7 persists; N2–N6
constant-honest-domain obligations remain unproved. Kernel-family provenance
is in `kernel-review.json` and `extra-kernels.json`; full transitive taint
coverage remains incomplete. No timing samples. V373/V374 OPEN/P.

Five native scopes exited 0; every scope has target/revision/wall/cgroup data
plus GNU-time RSS/swap logs, consolidated in `resource-summary.json`.
`closure-receipt.json` validates new source, registry, binary, disassembly and
PC bindings. No unchanged full regression was repeated. The historical A/B0
packet and validator evidence are reused for their original identities only.
No formal premise was removed/added/weakened or moved into capped trust T.
Target not yet established. See the current parent AUDIT.md and V374-PLAN.md.

`lock/lockfile.diff` is the zero-context presentation of the committed change,
so blank diff context does not create whitespace-check noise. The exact original
Cargo update diff remains in `lock/receipt.json`.
