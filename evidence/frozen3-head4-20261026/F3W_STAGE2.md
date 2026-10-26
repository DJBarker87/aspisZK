# Stage 2: same-submission source log factorization

Checked F3W_Runs.accepted constructs F3V's Evidence plus the SAME successful
TX1 call, for each accepted byte submission and H. No independent native pair
or native fixed-hash realization is introduced. F3W_SourceLog.evaluated uses
that same call and Evidence.second to identify the source eval's exact TX1
and TX2 ordered logs and saved checkpoint. F3W_FirstLog.log and
F3W_SecondLog.log factor these logs into preparation, batch0, writer, reader,
batch1. These are intermediate source facts, not the requested raw model join.

Attempts 001/002/004/005 passed, standard axioms only; 003 failed development
elaboration (underconstrained dictionary arguments and a missing import), then
004 fixed those causes. Failed 003's recovery sorryAx print is excluded from
proof evidence. No timeout or memory kill; no unchanged rerun, cap increase,
parallel own scope, Kani/Rust/SBF/ELF build or package replay. Full per-attempt
source/dependency/command/status/time/RSS/swap/axiom receipts accompany this file.

Before/after deployed theorem: unchanged Rc2_Top.deployed. No ledger premise
removed (zero deletion credit); no headline or non-vacuity proof attempted.
Next: combine the factorizations with F3V's preparation/model/checkpoint facts,
then canonical input transport and the SAME charged collision experiment.
