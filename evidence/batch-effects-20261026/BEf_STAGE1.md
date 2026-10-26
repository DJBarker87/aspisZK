# Recovery and checked interpreter stage

Recovered snapshot 6510b04661. Six charged Lean attempts, zero Kani.
BEf_003/005/006 successfully check the current Carrier/Pure/Batches sources;
001/002/004 are retained failures. No timeout/memory kill. Exact command,
source hashes, dependencies, revisions, exit/wall/RSS/swap and axioms are in
the original receipts; BEf_RECOVERY.json indexes the recovered attempts.

BEf_Batches.current/stage preserve full Result and ordered attempted-query
log on all source-syntax outcomes. BEf_Pure.exact preserves a chosen carrier
for the defined pure interpreter. Those definitions do not prove that native
execution uses that interpreter. No top statement changed, no ledger row
removed; L166 is still open. No new trust item or hypothesis was installed.

Further source inspection confirms the batch only receives immutable proof
bytes and allocates local fixed-size scratch; its Aeneas tree result includes
scratch outputs. Existing Port4B_Rejection/NativeReject already document that
several emitted rejection tails return panic instead of Rust Parse/Merkle.
Do not promote existing accepted-only refinement to all-Result equality.
This known extraction discrepancy is not a shipped Rust vulnerability.

No shipped/cfg(kani)/key/other-prefix edits. ELF pins are inherited, not
reproduced. No package replay. Host continuation will use the existing SInt2
workspace and runner, one admitted 6G/8G/Swap0/Tasks64 scope at a time.
