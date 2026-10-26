# RPx stage 0: scope and obligation

Assigned branch codex/cx-rejected-prefix-20261026. No shipped changes or Kani.
Read the repository Security and proof discipline, common/local rules, S2 ownership,
lead plan, diagnosis, route-B adoption, interface, SInt2 and Rc7 handoffs,
RowOrder_FrozenSchedule, F3X and GExq evidence.

Before: Rc7_Top.deployed has actual 83T/26P/13G and deduplicated
89T/31P/13G. L181 is a deployment-only obligation, NOT a literal argument
of that theorem. Removal needs a proof of rejected-prefix accounting on
its actual constructed F3X account; an alias or fewer wrapper arguments
would provide no credit. Runtime rejection is zero failure mass; accepted
source/model joining stays collision-aware. No equality of rejected source
and model logs will be presumed.

Plan: exact rejection log retention, duplicate-aware accounting, all-outcome
budget and charged bound, frozen3 batch/checkpoint schedule, actual-top
composition and non-vacuity, then expanded inventory/recount. New modules
RPx_ only. At most100 Lean invocations including dependency builds,0 Kani;
use the complete budget unless an explicit stop rule intervenes. Existing
launchers and coherent SInt2 objects only; one 6G/8G/Swap0/Tasks64 scope at
a time, -M7000. Reservation logs precede scp; wait at contention barriers.
No package replay or ELF rebuild trigger (no shipped source modification).
