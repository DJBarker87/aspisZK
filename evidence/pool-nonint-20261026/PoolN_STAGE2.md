# Stage 2: local guard matrix and verifier reuse

Complete native helper checks use arbitrary buffers, balances and an arbitrary
byte index for pointwise frame, with exact source errors. No bytes are replaced
by digests. The actual allocation-with-rent and allocation-with-seed helpers
reject before any CPI; NoEffects makes an unexpected CPI/close fail. Actual
close rejects before tombstone, refund, assign or resize, and preserves both
balances. Native helper results are still local, not a whole dispatch theorem.

KANI005/006 pass actual complete ASPX on the specified shard/authority layouts
for both checkpoint lengths. KANI007 passes all six fresh role sizes on both
lengths. KANI008 passes192 but its1768 post-create scan/frame test times out;
no unchanged retry is permitted. KANI009 onward cover the remaining individual
helper gates; their receipts are authoritative for exact status/metrics.

PoolN_Verifier composes existing checked source V1 occupied zero rejection,
V1 no accepted reinitialization, V2 complete heap frame and disabled admission.
It reuses Hist_/Hiq_/D189 objects and retains their named source/SDK/allocator
boundaries; it does not replace those boundaries with a lifecycle assumption.
PoolN_Effects preserves the exact error and complete prior ordered effect list
when a prepared-plan guard rejects; arbitrary close/reassign/realloc/CPI suffix
code is not invoked. It is a control model composition, not a source instance.

LEAN003 passes four verifier theorems. LEAN005 passes three effect laws.
LEAN004 failed on reserved identifier prefix, corrected to prior.
LEAN006's head? simp unfolded replicate and reached recursion depth; rejected.
Replacement uses a cons head with symbolic replicate tail length, no cap change.
No rejected sorryAx output is accepted as evidence. Only green printed audits
count. No shipped source/ELF changed, no runtime trust item added, no global
row or missing handler law discharged by these local results.

Next: literal contiguous source prefixes up to each rejecting state/payer guard,
with source-byte offsets/hashes and native reachability covers. These remain
primary-role slices unless a complete handler/alternate-role join is proved.
