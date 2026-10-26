# Per-step continuation (fresh allocation)

Branch `codex/cx-prover-rw-20261023`, base `5d97a425c5`.
Allocation: 100 Lean attempts, 20 Kani runs; Env-J 23700–23999.
Read shared pv-common rulings (a)–(d), r1p-common, local-lean and root
security/proof discipline. No production or existing proved module edits.

V164 before: owned compression/list equation proved, shipped correspondence open.
V163 before: whole proof/audit `data … = model` remains an explicit antecedent.
Callback remainder inherited: 31. No ledger row or endpoint premise removed yet.
Target not yet established.

## Source and sibling checks

At start pv-cb head is `55975ee0c6a68efbaab37317eca3209dbb03509d`.
Its worklist includes op223, op250 and all source callbacks in V169–V267
except the separately installed/assigned entries. Read-only use only; check
its current head again before any callback installation.

`generate.py` takes the literal shipped compression function and its exact loop
body from `crates/aspis-statement/src/logup.rs`. Generated wrappers expose the
post-state without modifying arithmetic. An indexed owned arity-16 reference
retains the final power update. `--check` requires exact generated text.
This is a checked textual association, not yet native whole-loop correspondence
or a kernel theorem about Rust machine execution.

## Split table

| Harness | Bound | Result |
| --- | --- | --- |
| `compression_state_step` | 2 | timeout240s, exit124; no certificate |
| `compression_accumulator_c0a` | 2 | running |

Expected time: optimized compilation, then one arbitrary-state native step,
with no stubs. Limits 6G/8G/swap0/Tasks64; 240-second timeout. Full arithmetic
and all eight output coordinates remain present. A timeout requires a smaller
successor, never a larger cap or an unchanged rerun.

## Lean23700

`PV_RW_CompressStep` passes: exit0,2.93s,4304028KiB RSS,zero swaps;
five standard-axiom reports. Exact modeled source-step sequence agrees with
owned step and its arbitrary-length Result iteration equals the retained fold.
No native machine/source association is inferred; V164 and V163 remain open.
Receipt and dependency manifest are committed alongside the exact input.
