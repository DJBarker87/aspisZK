# Verifier CP write certificate

PoolT_Write.accepted_verifier_writes_copy is checked in L047. It starts from ONE
accepted native wrapper execution with fixed original Entry and returned saved/post/final;
concludes the same native owned child returned saved, saved length1768, complete actual
account2 post-heap bytes equal saved, account/ambient/counter frames and every other-cell frame.
It removes Hist_CommittedPayload.copied's independent savedSize hypothesis using the actual
owned-call checkpoint snapshot and length check (PoolT_Verifier.returned_size, L002).
This is a local interpreted native-wrapper/source result, not a complete canonical runtime
history/source-to-ELF/refinement result. Existing AeneasExtraction, TrustedStd, allocator,
SDK and runtime interpretations remain; no new trust item and no global ledger removal.

L001 has a rewrite-direction development error, fixed in L002. L003/L045 fail inherited
history imports; L004-L044 build41 missing unchanged dependencies. They were then avoided
in the local CP theorem; no imported source was changed. L046 has a missing namespace,
fixed in L047. A shell printf octal error prevented one prospective launcher configuration
from loading; no Lean invocation occurred at that point. No launcher was modified.

Planner K001 complete decomposition, K002 error split, K003 first-checkpoint output,
K004 repeated lane0 progress output timed out at90s. K005 selected sequence/Bitwuzla
terminated with Kani cbmc_output_parser.rs:470 unknown variant ERROR, not a proof or
counterexample. All are retained and excluded. No timeout rerun unchanged, cap increase,
memory kill, package replay, shipped-source change, ELF rebuild or key/account operation.
