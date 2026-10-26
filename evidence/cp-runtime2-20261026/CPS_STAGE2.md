# Parent settlement and source recorder

Target not yet established; deployed ledger delta remains zero.

Recovered CPS_L001--006 from committed capacity snapshot 09d093f3fd.
Six attempts had run, five successful and one corrected elaboration failure
(L003, excluded). No Kani run had occurred. All current source snapshots match
their successful receipts. No work has been replayed unchanged.

CPS_ParentStatus.success_iff identifies final outer/inner Result success with
CPP_Atomic.committed. The sites filter and settled status use THAT final reply.
CPS_FailedParent.accepted_copy retains an accepted native copy followed by an
actual modeled parent error, rollback and no committed sites. Thus CPI success
must not be substituted for parent success.

CPS_BankSource.step_effect and CPS_BankRecorder.result/events establish ordered
state-threaded source effects on the same supplied CPP bank actions. New
CPS_BankTransaction.source_result composes their bank/event result with atomic
settlement determined by the final reply. query_frame retains all reached
source queries, including on parent failure. failed returns the original bank
and rollback event. No source action list or final reply is inferred from a
validator executor; this remains an explicit source-refinement boundary, not
runtime trust. No history fields or physical key pairing are silently assumed.

New attempts L007 (CPS_ParentStatus) and L008 (CPS_BankTransaction) both pass;
full target/command/source revision and sha/dependency fingerprint/exit/wall/
RSS/swap/caps/axioms are in their receipt.json files. L007 wall 2.149520732s,
RSS 5315376KiB, swap0; L008 wall 2.025427991s, RSS 5311180KiB, swap0. Standard
axioms only. Exactly one 6G/8G/swap0/tasks64 scope at a time with -M7000 and
existing reservation admission; no retry or cap increase. Budget 8/100 Lean,
0/10 Kani. No release replay or release result; compiled caches reused.

No shipped file, feature, wire format, dependency lock, toolchain or artifact
changed. Inherited default f8c0ec72..., devnet 63ad3e9c..., Pool 121f3e29...
pins remain historical; no ELF rebuild trigger. No wallets or keys touched.

Next: distinguish local Nat cell identity from physical public-key identity,
derive positive funding in a transaction-boundary-loaded bank model, and audit
exactly which further source/runtime premises survive in the conditional root.
