# All-Result/effect association boundary

The actual shipped Rust tail (candidate.rs:193-205) returns Err(Parse) on
nonzero padding, after all leaf hashes and before multiproof verification.
The retained emitted loop body returns `done (idx,val,none)` on that branch;
its enclosing emitted tree decodes `none` as `fail panic`. That distinction
is already proved locally by Port4B_Rejection.padding_result_differs and
Port4B_NativeReject.nonzero_padding. It must not be silently hidden behind an
acceptance Boolean or the successful-result projection.

The BEf native fixture uses the FULL verbatim batch_merkle_values and
a complete fixed-length proof, all-zero queries/openings, a nonzero last
padding byte of the first tree slot, zero roots and real SHA-256. For TX1
it selects slot0; for TX2 slot3. The complete native bodies both return
Err(Parse). This is checked native fixture evidence of reachability, not a
complete Lean execution of those large physical buffers. It is not a
shipped verifier vulnerability and does not yet refute a full native-to-Lean
instance with every lowered runtime condition supplied.

D188's AeneasExtraction contains stage1/stage2/digestSource value equalities.
It has no mutable allocator/account/pending-weights or rejected-log projection.
BEf_ExtractionGap will separately audit this precise logical insufficiency.
Adding a new premise asserting the desired native effect correspondence
would retain L166, not discharge it. No such new premise is installed.

The two open tasks are distinct: correct/justify all-Result lowering of the
rejected tails, and establish native mutable-carrier/effect association on
both batch calls and their prefixes. The generic BEf interpreter rules and
native fixtures are support for those tasks; neither supplies that endpoint.
