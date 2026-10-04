# R732: Selected ABC norm

Canonical Lean target: `AspisV8R19/R732SelectedAbcNorm.lean`, SHA-256 `2e4f889ceb920427cb655715f1201b65a77cd28b817ba9396fee0b125609f695`. Final focused run `1791133847626223000` used source revision `84de168cff730747b8193c17a5badb517b4b43c2`, Lean 4.32, `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The final target exited 0 in 0:01.45 with peak Lean-child RSS 3,266,248 KiB and swap 0. Its complete `#print axioms` output contains only `[propext, Classical.choice, Quot.sound]`.

Over any field with `2 ≠ 0`, R732 proves that two unit-circle points with `x1 - x0 ≠ 0` have nonzero selected ABC norm:

`(y0 - y1)^2 + (x1 - x0)^2 ≠ 0`.

This is exactly the `b^2+c^2` expression for `r17_host_relation`'s `abc = [x0*y1-y0*x1, y0-y1, x1-x0]`. The proof derives unit dot product, zero area under a contrary zero norm, then `x1=x0`, contradicting the explicit inverse condition.

The evidence preserves both focused proof failures `1791133823633340000` and `1791133838284459000` and final green `1791133847626223000`. It does not establish the selected source circle equations or successful `try_inv` condition, and makes no callback, oracle, privacy, or security claim.
