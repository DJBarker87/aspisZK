# Source-to-literal positive-row challenge simulation

RawSourceLiteralSamplerStep proves that a reached ordinary source call emits the same challenge and updated state as the literal sampler. Its premises identify the prior state, framed payload and one common oracle. The three digest equations and source challenge conversion are derived from the actual trace; the desired output equality is not assumed. Rows are below25 and nonzero.

RawSourceLiteralTraceLift composes those results over a positive-row suffix. It proves equality of the extended literal/source prefixes and the final state, retaining the starting-state equality, frame bounds, common oracle and row-count premises. It deliberately excludes row0, whose public initializer is different. RawSourceChallengeCarrier identifies the source challenge's coordinate representation with the exact field decoding used by the actual semantic-round proof.

All three focused native Lean4.32 compilations passed in about2 seconds each, with zero process/cgroup swap. The one-step and carrier printed axiom reports contain only standard axioms. The trace-lift compile did not print axioms; its separate import-only audit is pending and no audited release result for that target is claimed. Each receipt records source revision and exact bytes, object, imports, time, process RSS, admission inventory and capped execution. Process RSS is about4GiB; sampled charged cgroup memory is smaller because shared mappings were already charged elsewhere.

These checks reused a cached coalesced import namespace. Its resolved object hashes are retained in the import/preflight pins; namespace union and a focused compile do not establish unified source/owner correspondence. That clean release build remains open. No full regression or dependency rebuild was performed.

Remaining source/literal obligations: the special initial row0; full25 composition from the actual public initializer and strict framing; later circle/fold/query rows; commitment/opening binding; top-level actual acceptance-to-Checks and universal resource/query accounting. The complete100-bit soundness and private-spend release claims remain open.
