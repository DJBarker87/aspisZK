# R539: coupled H1/G correction passes the retained edge case

The changed optimized diagnostic compiles and passes the one `zero-low22` synthetic case that defeated the earlier sequential constructions. Choosing C1 jointly preserves the actual initial claim; choosing H1 jointly with the G compatibility equation preserves the remaining observations. No verifier change or new privacy/security claim follows.

## Exact construction and checks

R538 identified the required scalar equation `dot(wg-wr, rq) = gamma^27 * d[256]`, where d is the complete actual-source semantic difference. The new diagnostic evaluates the existing source H1 semantic-coordinate map M after correcting C1. It keeps all original 568 H1 equations and appends one coupled equation.

For quotient basis vector q_j and its source H1 pad m_j, the additional matrix row is

```
dot(wg-wr,q_j) - gamma * dot(M[256],m_j).
```

Its target includes the old source semantic difference and the first H1 pad. Thus it accounts for the H1-induced semantic change rather than assuming coordinate 256 stays fixed. A new full source semantic enumeration independently matches that prediction and the required scalar equation before the unchanged G solve.

The retained case checks:

- C1: four-row total-initial-claim solve, rank 4 with 2,250 kernel variables; all 16 original 108-row observation systems; 1,408 raw values, 48 point claims, 32 OOD claims; independent actual initial mask and relation claims.
- H1: original 568 equations at rank 544; coupled 569 equations at rank 545; all original legal-padding, raw/point/OOD/final and seven ordinary-polynomial checks.
- G: unchanged 626 equations at rank 600; all 271 semantic cancellations, p0 and p2, all seven combined relation coefficients, 88 raw values, three point claims, two OOD claims and 256 final values; actual encoding checks.
- The complete recomputed same-public source semantic difference after correction is zero.

All three systems are compatible, so no failure certificates were emitted. Earlier failures remain archived in R537/R538. Only this case ran.

## Proved boundary and remaining work

This is finite actual-source-based diagnostic evidence, not a universal theorem. The challenge history is synthetic: z=0, alpha=0, gamma=kappa=tau=1, accepted OOD parameters j and 2j, queries 0..21, and beta retained from another honest history. The R28 H1 helper retains six stronger ordinary-polynomial constraints. Commitment equality, shared-oracle simulation, seed support, adaptive conditioning, retries/stopping/publication and their probability losses are not proved here.

The first remaining proposition is universal joint compatibility for the actual observation system, including all legal same-public witness differences and adaptive or degenerate prefixes. The next construction should use all G compatibility rows and H1 source-map contributions instead of one case-specific coordinate. The entire published-view simulator and coherent pre-beta extraction/source soundness remain separate obligations.

## Exact release evidence

Frozen source revision: `6677d5f1310ff7373301fbd79f186278f772e68a`.

| Exact input | SHA-256 |
|---|---|
| Diagnostic caller | `0b69aa4ebb330a291cee674c4e4244eb214ea2b0add3c1353b41c36f398b7f22` |
| Correction helper | `639ca0c362bc41994b7ecdb8825e5914e5330e1e66b0a012d2a6998f6ff5b530` |
| Source H1 semantic map | `f16df7cda242734d0de3b64bdec1a1972123d763183211c2aedf22fa054141b6` |
| Selected payment terminal source | `957060c7556d2a0365c1cb3d2bf0576a72399c6c20bfbb47ea531f110dba54f5` |
| Immutable executable | `96860a34d439b0c3c2d1b934f7ae1070397d5bc88a81e37634a1bcd6dfca20f4` |

| Target | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| Changed focused optimized build | 0 | 35.37 | 594712 | 0 |
| Single coupled source-map/matrix run | 0 | 56.81 | 264188 | 0 |

Rust 1.94.1, optimized/offline/locked/jobs1, exact selected flags, and visibly compiled `-C overflow-checks=on`. Both jobs used 5 GiB high / 7 GiB max / zero swap / 128 tasks. The named heavy phase is source-map construction and the H1/G finite-field eliminations. The initial build invocation failed before Cargo because PATH omitted cargo-bin; its separate log is preserved. An earlier type-error snapshot is missing, as explicitly recorded; no missing bytes were reconstructed.

Exact source snapshots are content-addressed. Complete scripts, source checksums, fingerprint, logs and receipts are in `evidence/r539-coupled-h1-g-stress/`. The lead verified source/binary/log checksums, resource outputs, selected flags, overflow mode, and the single-case completion. `#print axioms` is not applicable: no Lean theorem was compiled for this diagnostic.

The selected verifier, security parameters and 999,790 / 999,532 CU results are preserved. No CU benchmark or unchanged regression suite reran.
