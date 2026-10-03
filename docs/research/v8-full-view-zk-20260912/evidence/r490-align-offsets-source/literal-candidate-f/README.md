# R490 literal candidate f

This archive records a successful Aeneas translation only. It pins the selected
LLBC SHA-256 `a3295333237b0dfad164b826a6d8ce6b2d183d177ca1453489e0e1d2a74a2698`,
source revision `4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35`, and R497 translator
binary SHA-256 `85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b`.
The translation exited 0 in 0:00.28 with peak RSS 65,472 KiB and zero swaps.

The focused adapter replaced only the `Aeneas` imports with supplied cached
constituent imports. Its exact source hashes and the unmodified raw generated
modules are both retained. The adapted `Types.lean` focused compilation exited
0 in 0:01.01 with RSS 2,531,984 KiB and zero swaps. The adapted `Funs.lean`
focused compilation exited 1 in 0:00.98 because the old cached library has no
`Aeneas.Std.Usize.div` or `Aeneas.Std.Usize.rem` aliases. Its complete log and
receipt are retained.

This is not a Lean proof. In particular, the actual helper remains unproved.
