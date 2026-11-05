# Own runner repairs

Seed preflight 1 failed before admission/launch: owned host directory absent when opening barrier log. Added mkdir(exist_ok=True) before opening the log; reservation and validation unchanged. No Kani/Lean/extraction allocation consumed. Original failure retained in NHP_NATIVE_SEED-initial.log.

K005: own snapshot attempted to move &mut u64 through Ref. Changed snapshot to copy the u64 via double dereference; frame checks unchanged. Compilation rejection consumes one native allocation.

K027: generator introduced a stray leading quote at the start of the new constructor-predicate harness. Removed the quote; no predicate/domain change. This compiler rejection consumed K027.

Validator strengthened: parse all printed axiom names, check shape source occurs in the compiled patch, compare guard body directly to frozen Git, and pin adopted extraction bytes to successful tool outputs. No invariant weakened.

K068: SDK table parser included the wildcard _ arm, so generation failed. A chained shell command incorrectly continued to the runner with the prior metadata patch and a nonexistent SDK harness; K068 records the rejected stale-input launch, no semantic credit. Excluded wildcard and now sequence one-off generation/launch as separate calls (campaign already checks generation success). K069 is the corrected first SDK-word attempt, under the same intended harness name.

K095: added Rc identity/count frame checks used std::rc in this no_std crate. Replaced with alloc::rc; no predicate weakened. K095 compiler rejection consumes one allocation. Corrected payer-alias begins K096.
