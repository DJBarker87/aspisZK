# R725: Seven-coefficient completion

Canonical Lean target: `AspisV8R19/R725SevenCoefficientCompletion.lean`, SHA-256 `85c6e655c46ee5aa1d858fff6d4e5f557051e9c017d07e3b2537d17f909143c0`. Final focused run `1791131674152374000` used Lean 4.32, `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The final target exited 0 in 1.54 s with peak Lean-child RSS 3,265,952 KiB and swap 0. Both complete `#print axioms` outputs contain only `[propext, Classical.choice, Quot.sound]`.

The first theorem uses `evalSeven d alpha = 0`, `d 0 + d 4 = 0`, zero rows 1, 2, 3, 5, 6, and explicit `1 - alpha^4 ≠ 0` to prove every coefficient is zero. The second theorem covers the fourth-root branch: with zero rows 0, 2, 3, 5, 6 and explicit `alpha ≠ 0`, it uses coefficient 1 as the pivot and likewise proves every coefficient zero. Thus no fourth-root branch is silently excluded.

All three focused records are preserved: two routine proof failures (`1791131647311734000`, `1791131665086391000`) and final green (`1791131674152374000`), with the exact R652 dependency and runner.

R725 is conditional seven-coefficient algebra only. It makes no actual challenge law, witness compatibility, native execution, privacy, or security claim.
