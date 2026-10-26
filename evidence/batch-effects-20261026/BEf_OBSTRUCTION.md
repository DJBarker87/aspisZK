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

## Reachability strengthened by BEf_R002/R003

The earlier direct-call limitation is now resolved for native verifier
reachability. The pinned adopted transfer-13 compact proof and public bytes
succeed in both native verifier transactions. From that same pair, actual
prepared queries give first-tree node counts138 and163. Mutating only the
first padding byte at32775 causes TX1 to reject with Parse after10 leaf
hashes. Mutating only batch1 padding at47015 still lets TX1 succeed with the
changed proof; its returned checkpoint then passes resume and TX2 rejects
with Parse after12 leaf hashes. Complete verifier entry functions are linked
unchanged from the shipped crate; no source child or hash stub is used.
The SHA backend is real host sha2, not a new source-to-Solana-ELF claim.

K006/K007 additionally check the exact terminal source slice with arbitrary
scratch values/suffix and a singleton live index; both prove Parse, scratch
frame and no suffix digest, with a reached non-vacuity cover. K008/K009 are
scoped to the ACTUAL captured fixture index sets and arbitrary roots; their
results must be read from their receipts, not inferred from K006/K007.

The Lean result BEf_Counterexample.rejected_batch_tail is explicitly LOCAL:
it compares the two pending-return encodings, not an evaluated full concrete
57607-byte fixture. Combined native fixture and source-slice evidence locates
a real all-Result lowering discrepancy. It is not a formal kernel replay of
the complete native-to-Lean execution, and it does not establish a shipped
acceptance vulnerability. L166 remains retained, with zero premise credit.
