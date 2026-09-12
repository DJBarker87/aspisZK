# Same-body authenticated terminal boundary — 2026-09-12

This checkpoint closes three deterministic joins that were previously kept
separate.

1. `FSSemanticAuthenticatedRootBridge.successful_runs_bind_semantic_roots`
   proves that successful semantic parsing and selected q22 authentication of
   one literal body make the semantic wire's two roots equal the chronological
   C1 and C2 root cuts. The roots are constructed from the parse and the
   authenticated run; no caller-supplied root-coherence certificate occurs.
2. `FSLiveSemanticTerminalInput.successful_run_constructs_terminal_input`
   constructs the 84 ordinary point claims, ten point coordinates, semantic
   challenges and carried scalar from that same parsed body and successful
   semantic-prefix execution.
3. `SelectedTerminalClaimMapping` maps those claims to the selected Rust
   terminal's three 16-column opening rows, ten mask-only fields, H and G at
   the exact body slots. It also connects the literal equality-factor and
   helper-tail expressions to the existing V7/source algebra.

The root theorem deliberately permits the semantic and Merkle runs to begin
from different oracle states. It proves deterministic same-body identity,
not yet the required chronological splice into one effectful verifier run.
Likewise, the terminal input and claim mapping establish provenance and
indices, not semantic-terminal acceptance.

## Poseidon source prerequisites

`SelectedPoseidonGenericAlgebra.lean` records the exact width-16 external and
internal linear layers and pow-5 rounds over a generic commutative ring.
`SelectedPoseidonCoordinateSlice.lean` instantiates one actual chronological
trace-table coordinate over `QM31[X]`, with the selected block/local selector
MLEs and structural evaluation/substitution identity. These are retained as
green prerequisites. The degree-27/Boolean packing bridge remains in progress
and is not part of this checkpoint.

## What remains at this boundary

- construct the literal selected semantic/copy/Poseidon terminal result from
  the mapped openings and authoritative public/context inputs;
- connect it to the callback and terminal-zero event in the complete
  successful verifier execution;
- splice semantic, OOD, authentication, query and later-response scripts into
  one chronological run rather than compare separate successful runs;
- prove actual adversarial random-oracle coupling and resource-bounded
  extraction, then compose all accepted failure classes;
- complete adaptive full-view zero knowledge and matched all-reachable CU.

The proof body remains 40,282 bytes and this work assigns no security credit
to grinding. It changes neither the wire nor production acceptance.

## Focused evidence

All commands used Lean 4.32.0 on the NUC with a pinned V7 Lake dependency
path, the private current-worktree overlay, `-j1 -M8192`, and a systemd scope
with `MemoryHigh=8G`, `MemoryMax=9G`, and `MemorySwapMax=0`. This is cache
reuse, not a clean first-party dependency rebuild.

| Leaf | Exit | Wall | Peak RSS | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `SameBodySemanticWire.lean` | 0 | 2.70 s | 6,555,024 KiB | 0 | standard only |
| `FSLiveSemanticPrefix.lean` (dependent replay) | 0 | 13.94 s | 6,741,396 KiB | 0 | standard only |
| `FSSemanticAuthenticatedRootBridge.lean` | 0 | 2.77 s | 6,743,744 KiB | 0 | standard only |
| `FSLiveSemanticTerminalInput.lean` | 0 | 2.77 s | 6,710,824 KiB | 0 | standard only |
| `SelectedTerminalClaimMapping.lean` | 0 | 3.25 s | 6,747,348 KiB | 0 | standard only |
| `SelectedPoseidonGenericAlgebra.lean` | 0 | 11.80 s | 6,631,084 KiB | 0 | standard only |
| `SelectedPoseidonCoordinateSlice.lean` | 0 | 4.40 s | 6,624,316 KiB | 0 | standard only |

Here “standard only” means `propext`, `Classical.choice`, and `Quot.sound`;
no `sorryAx` or custom axiom was reported by the printed endpoints.
