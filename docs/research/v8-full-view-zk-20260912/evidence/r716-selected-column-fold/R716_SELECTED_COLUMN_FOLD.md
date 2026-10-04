# R716: Selected-column first-fold kernel

Canonical Lean target: `AspisV8R19/R716SelectedColumnFold.lean`, SHA-256 `1569a7f1e0b59b2959bbf3440586f2c7580300a2fd49f1ea7c21b238ee8dae01`. It was compiled at source revision `a5e3046384337bf9a833a613cc72ae440d23741a` under Lean 4.32 with `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

Final run `1791129566534423000` exited 0 in 1.65 s, with peak Lean-child RSS 3,293,972 KiB and swap 0. The four complete `#print axioms` reports for the layout, per-block cancellation, fold theorem, and top-zero theorem contain only `[propext, Classical.choice, Quot.sound]`.

R716 defines the source-shaped selected-column direction

```lean
r ↦ unitVector (base j + slot j) r - alpha^slot j * unitVector (base j) r
```

and proves its `firstFold 256 alpha` is zero for every selected column, `alpha`, and 256-block. It also proves the same direction is zero at flattened source codes 1020 through 1023. The proof keeps the four local fold slots symbolic and uses only the selected layout bounds and direct cancellation.

Evidence includes all focused R716 records: initial definition/type errors (`1791129504594920000`, `1791129540674639000`), the first helper-green run (`1791129554279780000`), and final axioms-complete run (`1791129566534423000`), alongside exact R710/R370 source dependencies and the runner.

This is a source-shaped channel-basis algebra result. It does not prove native execution, an actual H1 universal image theorem, source-to-model correspondence, a privacy simulator, or privacy or security.
