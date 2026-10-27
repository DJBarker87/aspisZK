# Hir stage 2: adaptive scheduler and native Pool guards

Target not yet established. Global ledger delta remains ZERO.

Hir_ScheduleSource.result and Hir_ScheduleLog.exact_reads identify the same
native-store run, full replies, rollback events, source call reads and adversary
oracle reads. Finite schedules are fixed before H and adapt to prior replies,
reads and store observations. Every invocation uses the actual release route
and full installed source wrapper; errors/divergence/allocator/copy/cleanup
failures preserve their reached successful reads and roll back ledger writes.
Hir_Choice.selected loads TX2 from the computed final store. Hir_FactoryLoad.entry
removes a separately supplied load2 equality in this NEW constructed family;
Hir_FactoryCharge.reads ties all its reads to the SAME Q1 choice program.
Hir_ScheduleTrace.classified/protection derive verifier checkpoint protection
for this operational family. This does not enumerate all deployed runtime actions.

Before/after qualification: the original T2R theorem accepts independent e1/e2
and delayed history/P2Prime laws. The new constructed family supplies entries
via source schedule/store loads. Those are different quantifiers, not yet a
universal strengthening of the original top. The causal writer of a selected
TX2 account still needs to be extracted from the complete deployed lifetime;
an unrelated caller-supplied accepted TX1 cannot be silently identified with it.
The partial-syscall experiment's probability transport remains explicit/open.

Native Kani (all checks, no stubs, actual SDK RefCell methods) passes:
- Hir_KANI001: actual borrowed zero guard rejects occupied192-byte checkpoint,
  every other byte arbitrary; bytes unchanged.512 checks,0 failures.
- Hir_KANI002: actual fresh-PDA planner rejects same occupied checkpoint;
  bytes unchanged.500 checks,0 failures.
- Hir_KANI003: actual close helper rejects192-byte checkpoint for BOTH actual
  prepared-plan sizes10000/8504; bytes and source/refund balances unchanged.
  All192 bytes and both balances arbitrary;717 checks,0 failures.

These are helper/source checks, not complete Pool dispatcher/lifecycle gates.
Aeneas zero/fresh extraction remains failed. No checked accepted intervening
checkpoint write or shipped-source security counterexample was found.

Kani used only an own host snapshot Hir_src: original production files plus
appended cfg(kani)-only Hir harness modules. Repository shipped files are
unchanged; no adoption or source-to-ELF claim follows. Default/devnet/Pool pins
are inherited, not rebuilt. Own source snapshots and harnesses are receipts.

Budget21/100 Lean submissions (16 passing,5 failed development versions),3/30
Kani,1 optimized Charon,1 Aeneas. Detailed source/dependency pins, exit/wall/RSS/
swap/caps and axioms are in each attempt receipt. All accepted new top theorems
print only standard axioms; failed development sorryAx prints are excluded.
No package replay or cap/heartbeat/depth change. No launcher/tool repair.

Remaining: selected causal writer/lifetime provenance; complete Pool create/
write/read/close/authority/owner dispatch proof; actual T2R continuation discharge
with a single2965 account event/loss and exact margin. L159 remains excluded.
