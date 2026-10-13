# Second-fold arithmetic certificate attempts

Target: `docs/research/100bit-spend-path-20261013/lean/SecondFoldBudget.lean`

## Successful import diagnostic

The smoke source `SecondFoldSmoke2.lean` imports only
`Mathlib.Algebra.BigOperators.Intervals` and checks
`Finset.sum_range_id` and `Finset.sum_range_reflect`. It compiled successfully
with Lean 4.32.0 using the pinned NUC `run2.sh` workspace. Exit 0, elapsed
0.78 s, peak RSS 1,674,984 KiB, swap 0. `SecondFoldSmoke3.lean`, which adds
`Mathlib.Tactic.NormNum`, `Mathlib.Tactic.Ring`, and
`Mathlib.Tactic.Linarith` and checks an `omega` proof, also compiled: exit 0,
0.83 s, peak RSS 1,767,388 KiB, swap 0. Source hashes and raw logs are
preserved alongside this receipt.

## Failed attempts

All attempts used `dombarker@100.108.41.90` (hostname `nuc`), workspace
`/home/dombarker/project-offloads/aspis-fs-generic-20261006`, via the existing
`run2.sh` with `ML=5000`, `MX=6`, `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, and `TasksMax=128`; the launcher reported 24 GiB existing
reservation plus this 6 GiB scope.

- Attempts `a`, `b`, and `c` used the broad `import Mathlib` and terminated
  with Lean interpreter memory exceptions. Their recorded peak RSS was between
  6,142,768 and 6,156,276 KiB, with zero swap. Attempt `a` also tried direct
  normalization of the 113-term sum; attempts `b` and `c` used a symbolic
  summation draft. A separate smoke source containing only `import Mathlib`
  and `#check Finset.sum_range_id` also hit the same memory exception. This
  isolates the immediate memory failure to the broad import/environment, not
  the particular sum proof.
- Attempt `d` used narrow imports and completed Lean elaboration at 1,783,160
  KiB RSS, zero swap, but the source had proof errors in the square-sum helper,
  a redundant `ring`, the polynomial sum simplification, and final arithmetic.
- Attempt `e` used narrow imports and subsequent mechanical fixes. It completed
  at 1,783,816 KiB RSS, zero swap, but still reported errors in the square-sum
  induction, a sum simplification recursion, and the final arithmetic. Lean's
  continued output listed `sorryAx` for dependent declarations; this is a
  failed compile and not a valid certificate.

At attempt `e`, the source SHA-256 was
`e09b85c12bd2a21edfcef469692b828fa369db7a93673437766b59659bcdca69`. The
exact NUC source hashes, stdout/stderr, and `/usr/bin/time -v` records for each
attempt are included in this directory. No package or manifest build was run.

## Successful focused compile (attempt `g`)

After replacing the umbrella import with the narrow modules below and using
restricted sum rewrites, the changed file compiled successfully:

- Source: `docs/research/100bit-spend-path-20261013/lean/SecondFoldBudget.lean`
- Source SHA-256: `60251f5fff5bfb3c7faba894a1879a733008b740fbc94d9e0ca9187a3fc1430c`
- Source revision: `7742957648c33cf045eb6a672e7c7cc796b61087`
- Exact target: NUC cached workspace module
  `sources/SecondFoldBudgetStage7.lean`, output
  `objects2/SecondFoldBudgetStage7.olean`
- Compile command: `./run2.sh second-fold-budget-r1-20261013g SecondFoldBudgetStage7 5000 6`
  (the runner invokes Lean 4.32.0 with `-j1 -M5000 -DElab.async=false`)
- Resource scope: systemd user scope; `MemoryHigh=4G`, `MemoryMax=6G`,
  `MemorySwapMax=0`, `TasksMax=128`; existing reservation 26 GiB plus this
  6 GiB scope
- Exit status: 0; wall time 1.72 s; peak RSS 1,826,376 KiB; swap 0
- Imports: `Mathlib.Algebra.BigOperators.Intervals`,
  `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Tactic.Linarith`,
  `Mathlib.Tactic.NormNum`, and `Mathlib.Tactic.Ring`
- `#print axioms exact_weighted_sum` and
  `#print axioms numeric_feasibility_certificate`: `[propext, Classical.choice,
  Quot.sound]`; no `sorryAx`.

Attempt `f` immediately before this success had ordinary proof errors because
`Finset.mul_sum` was not available from the then-current imports and because
`yRows` had not been rewritten to 113 in the square-sum goal. The successful
attempt adds the required narrow big-operator module and explicit rewriting.
The exact `f` and `g` source hashes, raw outputs, and time records are preserved
in this directory.
