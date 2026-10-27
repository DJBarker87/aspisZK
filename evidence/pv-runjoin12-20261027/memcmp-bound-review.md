# Bound correction from retained CBMC loop metadata

CBMC --show-loops on the exact retained Run04 model lists builtin memcmp. Aggregate array assertions include24×8×4=768 bytes for sibs,640 bytes for each public matrix,96 bytes for bits and32 bytes for each digest. Thus the earlier claim that25 bounds every reachable loop was incorrect;33 also does not cover these aggregate equality loops. Earlier incomplete runs establish neither equality nor a counterexample. All raw bounds/receipts remain intact.

The replacement compares every scalar word explicitly, with24,20 and8 iteration loops. All20 returned fields remain compared. Source calls, reference implementation, optimized flags, checks and unwinding assertions remain unchanged. No memcmp replacement/stub or assumed equality is introduced. Dynamic variants execute the actual root helper on both sides; fixed variants are separately named and retain the frozen-table distinction.

Run05 ten-minute review (06:13 UTC): full dynamic comparison still in CBMC, roughly4.5GB memory, no result. The metadata contains no stubs/contracts and unwind25. Continue only to the unchanged900s limit; no cap or backend-check changes. Presence of a memcmp symbol in a GOTO binary alone is not a reachability result; all unwinding assertions remain active and final verification is required.
