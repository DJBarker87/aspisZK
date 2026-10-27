# Bounded emitted callsite

ProverRw21Arity16Endpoint (37765) is checked. The only op223 call in the
retained FullFuns extraction consumes Array U32 16#usize after copy_tuple_values.
Agreement on those arrays preserves the complete endpoint Result, including
errors and mutable writeback. The dependent loop/material proofs are separate.

Read-only sibling provenance: codex/pv-cb-20261026 at
21fd275d99247ee891415db284c47f7955e775f8 has the analogous
PV_CB_Op223Callsite.endpoint simp pattern, used to replace broad reduction.
The source-law search in both sibling heads still returns no op223_source.
This proves caller transport, not a binding from the deployed native callback.
V164 remains {P_source_p6}; no endpoint premise is removed in this stage.

Native budget: all 10 slots spent, exact configurations and results retained.
The overflow-off override was rejected by Kani and not bypassed. Two restricted
laws passed (arity zero, unrestricted arity-16 values with lambda zero).
Timeouts and a checked MIR overflow assertion do not prove the unrestricted
callback law and are not classified as shipped-release ROW counterexamples.
