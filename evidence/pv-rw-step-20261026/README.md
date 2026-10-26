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
| `compression_accumulator_c0a` | 2 | timeout240s, exit124; split scale/add |
| `primitive_split::scale_c0a` | 2 | timeout240s, exit124; CaDiCaL, no reach checks |
| `primitive_split::add_c0a` | 2 | PASS0.37s |
| `compression_iterator16_next` | 18 | PASS11.79s |
| `scalar_mul_wrapper` | 2 | running, arithmetic refinement |

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

## Lean23701

`PV_RW_CompressBound` passes: exit0,2.44s,4306600KiB RSS,zero swaps;
four standard-axiom reports. Proves sufficient fuel = input length+1 for
arbitrary Result steps, specializes to17 for arity16, and proves the prefix
iterator bound. This does not cover compiler-generated memory-copy loops;
the native harness also keeps all unwinding assertions enabled.

Usage at this checkpoint:2/100 Lean,3/20 Kani launched. No row removed.

Native003 isolates the scale projection from the timed-out composed accumulator
and switches to Kani's documented built-in CaDiCaL. Still times out240s,
exit124,zero swap. No primitive certificate is inferred. Further split must
isolate multiplication/reduction, not repeat any of these harnesses unchanged.

## Lean23702 and literal extraction

`PV_RW_CompressReference` passes: exit0,2.70s,4312292KiB RSS,zero swap;
two standard-axiom reports. Exact step-source model = previously extracted
owned compression, all slices; bounded model with17 fuel = owned compression
on every typed16-cell array. No live callback installed.

The new literal compression step extracts and translates successfully with
unchanged pinned Charon/Aeneas. Both have independent receipts. A generated
new Lean module copies the exact emitted step body and adds source association
proofs. This is stronger source evidence, not a native full-loop certificate.

Native-input source audit compares234 production files in core/statement/cost
probe with the host preflight hashes: all match this base. The historical host
revision label is retained and explicitly distinguished from the branch pin.
This is not an artifact/release association. The full task scope still requires
actual source/native/effect adequacy, full proof/audit model equality and the
privacy endpoint/deployment conditions; none is silently dropped.
