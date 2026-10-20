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

## Stage 1: demonstrated backend obstruction

The premise “the prover's hash is Poseidon2” is false for the HashFn callback
that blocked the previous continuation. `hash-frontier.json` records exact
source spans, line numbers and SHA256 pins; `harness/hash-frontier.py`
rechecks them from the repository root without changing any source.

The concrete chain is:

1. `aspis-core/src/transcript.rs:45` defines
   `HashFn = fn(&[&[u8]]) -> [u8; 32]`.
2. `aspis-prover/src/lib.rs:82-91` defines `host_hashv` using
   `sha2::{Digest, Sha256}`, updating once per input slice and finalizing,
   then sets `HOST_HASH: HashFn = host_hashv`.
3. `masked_fixture_gate.rs:4,29` selects that HOST_HASH;
   `r1p_retry_gate.rs:54,89` passes it to both proof entrypoints.
4. `state_only_hiding.rs:399` and `state_only_entropy.rs:580` call this
   supplied byte callback for the mask seed and leaf salt. The source/D
   and refill paths likewise accept/call the supplied HashFn; neither file
   calls Poseidon2.
5. The program's `SolanaDigest` routes to `solana_program::hash::hashv`,
   matching the SHA-256 backend described in the core and prover sources.

In contrast, `aspis-statement/src/poseidon2.rs` implements the statement's
field-based hash: `permute_optimized(&mut [M31;16]) -> ()` and
`merkle_node_compress_v3(&[M31;8], &[M31;8]) -> [M31;8]`. Neither has the
HashFn signature. There is no byte encoding/framing adapter identifying
these with host_hashv. D90's component equality therefore cannot establish a
contract for the callback in this prover cone. Statement Poseidon2 and the
PCS transcript/commitment byte hash are distinct uses of hashing.

Per common rule 4, stop this item rather than prove an irrelevant backend
and call it source closure. No `stub_verified` was installed, no hash outputs
were postulated, and no symbolic hash/builder result is claimed. No Kani
job was launched for the wrong backend. This is a source-identification
obstruction, not a solver timeout or a counterexample to the desired builder
equivalence. The old `kani::any::<HashFn>()` diagnostic remains a harness
problem: selecting a concrete function pointer would remove that diagnostic,
but does not by itself verify an admitted abstraction for the function.

A sound continuation needs either a verified SHA-256 callback contract on
the actual byte framing (then per-function shipped/reference builder checks),
or an explicitly approved implementation-independent relational callback
proof that never assumes unmatched inputs have equal answers. Merely
substituting Poseidon2 would change the proved implementation. The concurrent
builder/SourceIdentification and ScanCoupling owners' files are untouched.
