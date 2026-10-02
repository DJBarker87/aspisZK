# R372: source-column compatibility fragment

R372 derives zero first-fold values for the defined 32-block source columns from an explicit injectivity premise on `t : Fin 22 → F` and `NeZero 2`. It applies R370’s generic kernel identity to obtain zero kernel evaluation for arbitrary dual vectors and linear combinations of those columns. An explicit extension embeds a 32-block column in a 256-block vector with zero values above block 31 and preserves the zero-fold conclusion.

The successful focused run `1790949125467117000` exited 0 in 0.99 s with peak RSS 2,293,128 KiB and no swap. It used systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`. Five complete `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The earlier incorrect 256-block draft is preserved with its source, log, receipt, and `sorryAx` reports.

The premises concern the mathematical `t` supplied to the defined source-column model. This fragment does not prove injectivity of actual q22 roots, Rust transport to these columns, joint legal-mask coverage, simulator properties, or security. See the [evidence bundle](evidence/r372-source-column-compatibility/README.md) for saved run records and source/cache inventories.
