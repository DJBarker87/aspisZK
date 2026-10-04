# R724 joint H1 witness diagnostic

A source-shaped field diagnostic went from rank 221 to full row rank 222 after adding one identified missing direction, `(d,s)=(47,3)`. The result is evidence about this finite algebraic matrix at one unsampled parameter tuple. It does not prove privacy, verifier behavior, or a security bound.

The matrix has 222 rows: 214 selected active-chord observations, three point observations, and five ordinary relation coefficients. Its columns are the 214 selected H1 core directions, the original 27 supplemental directions for `d=23..31`, `s=1..3`, and the newly added pair `(47,3)`. All 241 earlier columns and every row entry are byte-for-byte identical between the rank-221 and rank-222 captures. The raw 242-column matrix is saved as four QM31 limbs per entry, before elimination.

For the shifted tuple `z=[1,1,2,3,4,2,2,3,0,2]`, `alpha=7`, `kappa=5`, and `(a,b,c)=(7,5,-5)` over M31, the earlier 241-column matrix had rank 221. Its saved left-null covector has nonzero support on 44 active-chord rows and the point-0 and point-2 rows. Independent arithmetic over the saved matrix confirmed the covector annihilates all 241 old columns. The omitted-pair transpose check independently found the first nonzero pair `(47,3)` with value `1909084209`; multiplying the old covector by the appended column gave `(1909084209,0,0,0)` modulo `P=2147483647`. The 242-column matrix then had rank 222 and eight supplemental pivot columns. The complete pivot metadata, old covector, raw matrices, and checking scripts are included in the evidence directory.

The diagnostic checked the selected R16/two-swap order table, first-fold zero for each direction, four zero high-tail coordinates, inactive balance, and a 23×3 same-slot low-observation constancy preflight. The run did not separately compare all 214 core observations before and after the low correction, so that preservation remains a source-shape/formal boundary here. The shortcut compares observations on `pair(d,s)` with the same-slot `pair(0,s)` for `d<23`. That is a low-23 constant-observation check; it is **not** the 88 observations at the 22 actual query roots. Lifting this shortcut requires an augmented 23-root normalization: the 22 selected roots plus root 1, with noncollision supplied by R691. `AugmentedQuerySection.lean` provides a 23-root section for its existing Fin32 domain; extending it to the full domain and binding it to the actual sampled prefix remain open. R682 separately proves full-domain normalization for 22 roots. The generic R682 prototype was not run in this task.

The shifted tuple `(u,v)=(2,3)` supplies algebraic chord parameters `(a,b,c)=(7,5,-5)` for the matrix calculation. These inputs lie in the CM31 subfield and are rejected by the selected OOD sampler. Do not describe this matrix as an accepted selected-prefix result. The diagnostic also uses the ordinary reference weight construction; it does not prove equivalence to the optimized tensor execution used by the selected verifier. No source callback or native verifier was edited or executed here.

The remaining work is to prove the joint 222-row minor symbolically for the applicable normalized source construction; bind that construction and its query-root normalization to the actual selected legal prefix; prove the selected challenge and shared-oracle law across adaptive retries; and finish the privacy simulator and explicit probability losses. The result here does not close any of those obligations.

## Run record

All three matrix-producing jobs used optimized Cargo release builds, offline and locked with one job, and the NUC cgroup limits `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. The C and D runs loaded the complete frozen R117 `RUSTFLAGS` file (SHA-256 `df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8`) and enabled overflow checks. Exact scripts, exit files, logs, source hashes, pinned source snapshots, cgroup invocation IDs, wall/RSS/swap receipts, and raw matrices are preserved under `evidence/r724-joint-h1-witness-diagnostic/`.

| Attempt | Parameter tuple | Columns | Result | Wall / peak RSS / swap |
| --- | --- | ---: | --- | --- |
| B2 | fixed `z=[1,1,2,3,4,0,2,3,4,2]` | 241 | 221/222 | 0.98 s / 181,500 KiB / 0 |
| C | shifted `z=[1,1,2,3,4,2,2,3,0,2]` | 241 | 221/222 | 23.48 s / 595,092 KiB / 0 |
| D | same shifted tuple plus `(47,3)` | 242 | 222/222 | 23.34 s / 597,924 KiB / 0 |

Attempt A's Rust build failure and the separate B launch failure are preserved as well. B2's runner did not set the complete frozen `RUSTFLAGS`; the C/D runs did. These are diagnostic-only Rust results, so `#print axioms` is not applicable.
