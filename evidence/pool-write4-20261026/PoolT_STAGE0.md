# PoolT write certificate work

Source anchor 546891795f5060bd2f71784bb9fee05b34bba001, branch codex/cx-pool-write4-20261026.
Read required S2 ownership/plan/diagnosis/interface and route-B addendum, common/local rules,
full lifecycle scope and PoolS/PoolW/PoolV/PoolU/Hist/Hiq/Hir/SInt2 handoffs.
Only PoolT_ modules/evidence will change. No shipped sources, keys or accounts change.
Budget 100 Lean invocations including dependencies, 15 missing-leaf Kani invocations.
Reuse coherent SInt2 host objects. Scope high6G/max8G/swap0/tasks64; Lean -M7000;
Rust optimized -j4. Initial host scope inventory: only init.scope, zero build reservation.

First target: original unrestricted pure planner decomposition on full production types,
retaining every error and output field. Comparing full original output with a fissioned
byte-matched implementation avoids asserting only a restricted coherent input class.
Then decoder/PDA same-snapshot joins and caller/canonical-action coupling; CP remains separate.
No closure or new runtime trust is claimed by the preflight.
