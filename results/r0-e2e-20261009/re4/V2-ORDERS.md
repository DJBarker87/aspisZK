# V2 orders, counted before implementation

This ledger was written while `onchain.rs` still used the R-E3 evaluation order
(with S1 subfield arithmetic, S2 tensor update, and S3 Karatsuba).
The input source hash is in `v2-order-counts.json`; the generating script is
`scripts/r0_re4_v2_count.py`. These are operation estimates, not measured CU.
All counts cover one complete V2 including the polynomial, line construction,
kappa powers, tau square, top-row recurrence, and final quarter.

Let C be the existing monomial-truncated chord map, D the cited dual fold,
G = D^T F, and w = indicator + sum_p kappa^(p+1) eq_p.
The existing scalar is <F, D(C^T w + tau e1 + tau² e2)>.
The alternatives evaluate the same pairing by linearity. The quarter stays
outside; no challenge, predicate or predicate order changes.

- Current: form the E weight vector, apply C^T, add the image rows, fold and dot.
- Scalars outside: form four K vectors C^T eq_p and C^T indicator. Pair
  G with them and e1/e2, then apply the E scalars. The literal six dense dots
  are counted, and a better variant exploits the image rows' three entries.
- Transpose onto F: form G in channel order [0,3,2,1], save its three image
  entries, apply C to G, then pair CG with three K tensors and the bit-table
  indicator. The sparse column generator is transposed by scatter, including
  the same top overflow correction. This is the selected order.

| Order | E×E | E×K | E×F | K×K | K×F | E adds/subs | K adds/subs | F mul | Estimated CU |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| current | 1039 | 6146 | 3838 | 3069 | 2 | 10506 | 3069 | 1568 | 8332083 |
| scalars_outside_six_dense_dots | 788 | 6144 | 0 | 15357 | 15350 | 6159 | 28657 | 6167 | 13331909 |
| scalars_outside_sparse_images | 788 | 4098 | 1 | 15357 | 15350 | 4112 | 28657 | 6167 | 11746594 |
| transpose_onto_F | 788 | 6146 | 3838 | 3069 | 2 | 10292 | 3069 | 1568 | 7978749 |

Each order also has 18 F additions and one K negation. Counts include the
four source-level multiplications in `powers::<4>`; an optimizer may remove
its unused final multiplication. Prices use R-E2 N=128 except E×E, replaced
by the S3 N=128 measurement (1,312.1953125 CU; R-E2 was 1,466.5625).

| Order | Product reductions | Operand %P normalizations | Canonical add/sub reductions | Explicit vector bytes read/written | Loop sweeps |
|---|---:|---:|---:|---:|---:|
| current | 198582 | 28422 | 546272 | 884592 | 45 |
| scalars_outside_six_dense_dots | 337648 | 24576 | 873037 | 1359392 | 69 |
| scalars_outside_sparse_images | 300828 | 16393 | 762545 | 1228368 | 65 |
| transpose_onto_F | 191805 | 28422 | 521217 | 951184 | 48 |

A product reduction is a call of the base Mersenne reducer: E×E=27,
E×K=18, E×F=8, K×K=9, K×F=4. `mul_qm31` additionally normalizes four
operand limbs; `mul_m31` normalizes one. Canonical add/sub counts expand the
entire tower (E×E=93, E×K=46, K×K=23, E add/sub=8, K add/sub=4).
This distinguishes source normalization work from multiplication reductions;
it does not claim LLVM retains every normalization.

Memory counts cover explicit vector element reads/writes, including zero
initialization. They exclude scalar temporaries, stack spills, decoding and
read-only index/coefficient table accesses. The source-level loop sweeps are:
current: 5 initializations, 1 indicator fill, 30 tensor levels, 3 weight scans,
1 half-vector copy, 3 sparse column sweeps, 1 combine sweep, 1 folded dot;
scalars-outside sparse: 6 initializations, 1 G build, 30 tensor levels,
4 weight fills, 4 half copies, 12 column sweeps, 4 combines, 4 dots (dense
images add 2 initializations and 2 dots);
transpose: 5 initializations, 1 G build, 30 tensor levels, 1 half copy,
3 scatter zeroings, 3 column sweeps, 1 combine, 1 indicator scan, 3 dots.
Each sparse-column sweep also walks the fixed 512-entry overflow table once;
only its 256 nonzero entries cause field operations. Each tensor level scans
its current width, summing to 1,023 pairs per point.

Selection: transpose onto F. Its arithmetic estimate is 353,334 CU below
current, while its explicit vector traffic is 66,592 bytes higher. Memory
traffic is reported, not assigned an invented primitive CU price. The other
orders spend much more on K-side chord products. No 6.5–7M prediction follows
from these particular exact schedules. The subsequent SBF measurement will
resolve whether the arithmetic saving survives the scatter overhead.
