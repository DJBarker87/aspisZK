# Own runner repairs

Seed preflight 1 failed before admission/launch: owned host directory absent when opening barrier log. Added mkdir(exist_ok=True) before opening the log; reservation and validation unchanged. No Kani/Lean/extraction allocation consumed. Original failure retained in NHP_NATIVE_SEED-initial.log.

K005: own snapshot attempted to move &mut u64 through Ref. Changed snapshot to copy the u64 via double dereference; frame checks unchanged. Compilation rejection consumes one native allocation.

K027: generator introduced a stray leading quote at the start of the new constructor-predicate harness. Removed the quote; no predicate/domain change. This compiler rejection consumed K027.
