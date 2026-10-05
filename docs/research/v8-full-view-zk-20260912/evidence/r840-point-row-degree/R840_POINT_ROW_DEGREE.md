# R840 point-row polynomial degree bound

R840 proves that the actual R745 point-row entry has total degree at most 60, uniformly for arbitrary `half`, `quarter`, `d : Fin 255`, `s : Fin 3`, and `p : Fin 3`:

`(polynomialEntry half quarter d s (.inr (.inl p))).totalDegree ≤ 60`.

The supporting theorem bounds the exact `pointWeight` used by R740 at degree 57. It starts from R836's degree-55 `sourcePointBasis` bound for the actual ten-coordinate statement points, preserves that bound through the selected `transportDual` and `extendFin1024` operations, then applies R838's exact gather/chord-transpose degree bound with the three source chord coefficients of degree at most 2. The R743 point observation has four such point weights; each alpha power has degree at most 3, so its two products and both differences remain bounded by 60.

## Exact verification

- Target: `AspisV8R19/R840JointPointRowDegree.lean`
- Final source SHA-256: `c6b51b8f66dd1f57bb21fd12757b83e3a74164c29ab155020ef01470b8c37b84`
- Worktree source revision at run: `9a0fc29a383d22e5cd2b9d5ad1333e29dcd54f63`
- Final run: `1791162215072327000-88f3beb1ea20`
- Exit: 0; wall: 3.29 s; peak child RSS: 3,308,056 KiB; swap: 0; Lean flags: `-j1 -M4500`; cgroup: MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128.
- Complete `#print axioms` output for each proved declaration: `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- Imports included unchanged R745 (`45e6b4689a0c1800900e2ad6eb642e81170f0bf99cbd397931daaa0bfc071f4e`), R836 (`7306220ec634a973f2ea02d2149b16c61dceba29f0f48471e9118346bcc93888`), and R838 (`ff305ae94095b84a2d6184252aa4b80cacd7bc5fe0ae823945388df28564ce86`). R838's source-weight degree proof was already green and cached before the R840 run.

The two failed focused attempts are preserved in `attempts/`: the first exposed an incorrect coefficient-field parameterization, and the second exposed an over-unfolding `simp [C]`. The final changed target compiled successfully after correcting those issues. Their logs and receipts are retained with their exact source snapshots. `SHA256SUMS` covers all files in this evidence directory.

## Boundary

This is a degree bound for the R745 point-row polynomials. It does not prove the analogous bound for every coefficient row or establish a uniform bound for the entire observation matrix; those remain necessary for the determinant degree argument.
