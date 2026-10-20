# Prover commitment continuation 3 — 2026-10-20

Branch `codex/cx-prover-commit2-20261020`, source `6593c0c21`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit3-20261020/`.

## Stage 0: frozen ELF gate passed

Rebuilt this branch on the host with Solana 3.1.13 / platform-tools v1.52,
the exact freeze features, locked offline dependencies and four jobs. Each
build ran in its own scope with MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. Expected work was incremental optimized SBF
compilation/linking. Before launch the three observed populated peer scopes
reserved 24 GiB; this sequential job added 8 GiB, below the 55 GiB limit.
Native RUSTFLAGS was `-C link-arg=-Wl,--threads=4`; exactly as in the freeze
it was unset only for cargo-build-sbf, whose target-specific flag was
`-C link-arg=--threads=4`.

| Program | SHA256 | Exit | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| Default verifier | dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34 | 0 | 42.234 | 648240 | 0 |
| Devnet verifier | fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78 | 0 | 3.009 | 204148 | 0 |
| Pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 0 | 32.417 | 644664 | 0 |

All three also pass `cmp --silent` against the frozen host artifacts.
`frozen-source-check.json` contains complete resolved normal/build dependency
inventories for each program (including all external crates), source hashes,
exact commands and resource receipts. `#print axioms`: N/A, no Lean compiled.
The ordinary native rustc initially rejected the SBF target for cargo tree;
using the pinned platform-tools rustc resolved that inventory-only error.
No SBF build was repeated.

Contrary to the handoff's description, `aspis-r1-cost-probe/src/lib.rs:20-21`
already guards `pub mod prover` with `#[cfg(feature = "prover")]` in this
rebased source. The program selects default/optimized-terminal/private-leaf-salts/
program-build, without prover. Neither program's dependency closure contains
`aspis-prover`; both do contain `aspis-statement` and `aspis-core`, included
in the inventory and source check. No refactor movement was required.
The conditional runtime reruns requested on an ELF mismatch were therefore
not triggered. Existing fixed-seed, 33/33 library/D78 and 8/8 P_R1 results
remain recorded in the previous continuation; they were not rerun unchanged.

The build logs retain SBF stack diagnostics also emitted for non-entrypoint
functions; exact identity establishes the same frozen bytes, not a new
stack-safety theorem. No shipped source, key, account or peer worktree changed.
