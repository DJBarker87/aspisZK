# SAME-call allocator sites

The root cannot be repaired by renaming `reserved : Bool` to `reservation : Reservation`. Both remain arbitrary unless attached at the actual primitive call. Existing named Allocator scope is retained; no new trust is proposed here.

The direct source path has at least two fallible filled calls, in source order:

1. resume: filled(v.final_len(), K::ZERO) after the last scalar read; for S2 this is64 K cells. Its complete error mapping is Error::Allocation. Box allocation of the Prepared occurs only after read_weights and the final-cursor guard, with returning/abort scope (aa).
2. tx2_common: BatchedWeights::new invokes filled(weights.len(), [0u64;4]) after resume, powers, inactive parsing, Merkle and geometry. At this reached call the SAME weights length is64. Its complete error mapping is also Error::Allocation.

Their runtime outcomes must be recorded at their separate invocation sites. Equating them is not justified by equal lengths: their element sizes differ (16 versus32 bytes), and they occur in different allocator states. A shared global Bool can represent both-success or first-failure on accepted/failing-prefix arguments; it cannot be silently asserted to be the exact general native Result-and-effect model of both invocations. No counterexample to the security bound is claimed; this is an outstanding source-refinement obligation.

Correct implementation route: instantiate the native filled oracle at each entered site with the CLOSED filled law and the actual allocator event at that site, preserving error/abort prefixes and threading private allocator state. The complete full-result model needs that state or site-indexed event interpretation; successful-return totality is never assumed. NJC_FilledClause.source already proves the exact logical ZERO64 value for either Reservation arm. NJJ map_allocation64 and pending_start cover the actual standard map_err carriers; they do not create the missing allocator event by an endpoint hypothesis.

NJJ does not replace this work with a freely supplied pair of flags, a stronger allocator-success premise, or a new trust row. The source module for the positive root must ultimately consume the existing named item at each literal filled occurrence.
