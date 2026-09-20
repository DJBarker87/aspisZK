# R15 exact-tower chord evidence

Date: 2026-09-20. Privacy source base `1906197f`.

## Proved boundary

`ExactTowerChord.lean::source_policy_chord_nonzero` instantiates the generic
subfield-circle result for the literal deployed tower:
M31 = ZMod(2147483647), CM31 = M31[i]/(i²+1),
QM31 = CM31[u]/(u²-(2+i)). It proves that the chord through two distinct
finite rational points, with both parameters having nonzero upper CM31
coordinate, is nonzero at every CM31-valued circle point.

The premises are the mathematical counterparts of successful source OOD
sampling: both rational denominators nonzero, upper coordinates nonzero,
and distinct returned points. The CM31 subfield characterization and
`2 ≠ 0` are proved, not caller assumptions. This is exact-tower algebra,
**not yet executable Rust refinement, source sampler probability, or privacy**.

## Retained certificates, smaller dependency graph

The old `V5ComponentCQM31TowerExact` source SHA-256 is
`75404d16b5a71f67146b91ca35739b111f81bb730beb77432267f2b5385cebe5`.
Its declarations from `P` through `QM31Exact`, including the symbolic
30-step non-residue certificate, are copied verbatim into `ExactTowerBase`.
Only namespace and imports differ. `tools/check_r15_tower_extract.py`
checks the old hash and exact declaration equality; it passed with exit 0.
The original file is unchanged. No nonsquare or field axiom was introduced.

The full old import failed under the 1800 MB Lean allocation cap, including
in an import-only preflight. The first reduced import also exceeded that
cap before any declaration, as confirmed by its own import-only preflight.
The replacement removes sampler dependencies and narrows tactic imports to
`NormNum.Prime`; the revised base compiled at an explicit 2600 MB cap.
No uncapped job, cold dependency rebuild or global replay ran.

## Exact checks

Cached workspace `/Users/dominic/ZK/AspisFormal`, Lean 4.32.0;
single thread, `/usr/bin/time -l`. All rows had zero swaps.

| Target / attempt | Exit | Wall seconds | Peak RSS bytes |
| --- | ---: | ---: | ---: |
| Generic olean, missing package-root flag | 1 | 2.64 | 669696000 |
| Bridge before generic olean existed | 1 | 1.21 | 668614656 |
| Generic olean with explicit `-R` | 0 | 8.50 | 1573453824 |
| Bridge importing full old tower, cap 1800 | 134 | 45.27 | 4406345728 |
| Full old tower import-only, cap 1800 | 134 | 84.44 | 4246765568 |
| Initial reduced tower, cap 1800 | 134 | 6.10 | 1920712704 |
| Reduced import-only, cap 1800 | 134 | 12.98 | 1911373824 |
| Revised minimal tower, cap 2600 | 0 | 16.31 | 2276507648 |
| Bridge, implicit numeral simplification | 1 | 14.61 | 2063106048 |
| Bridge, explicit projected numeral | 1 | 951.05 | 2063908864 |
| Final bridge, characteristic proof | 0 | 269.76 | 2061025280 |

The two long wall times are reported exactly as observed; their user/system
CPU times were respectively 2.13/2.96 and 2.58/3.05 seconds. The cause of the
wall/CPU discrepancy is not established. No timeout was treated as a finished
job, and no duplicate job was launched. The >10-minute failed run was reviewed
before continuation: it was terminal with an explicit unsolved numeral goal,
not a running aggregation; the replacement changed that proof to
`ZMod.natCast_eq_zero_iff`, at the same cap.

Failed bridge outputs containing `sorryAx` are error-recovery output, not
proof evidence. The final base certificate and all four bridge `#print axioms`
results contain only `propext`, `Classical.choice`, `Quot.sound`.

## Reproduction and remaining proposition

Compile the generic leaf and minimal base separately with `lake env lean`,
`-j1`, explicit `-R .../lean`, and `-o` outputs under an isolated
`AspisV8R15` directory. Generic cap: `-M1800`; base/bridge: `-M2600`.
Add that output root to `LEAN_PATH` inside the existing `lake env`, then
compile `ExactTowerChord.lean`. Retained local outputs are in
`target/r15-lean/AspisV8R15`; no production path is edited.

First remaining proposition: show that the actual successful Rust sampler
and selected query-point routine map to these exact-tower objects and circle
invariants, and that the selected optimized inversion agrees with the
nonzero field inverse. The existing Rust formula-seam library explicitly
leaves executable function equalities as hypotheses; importing it would not
discharge them. Query-address freshness, reach and publication probabilities
remain independent outstanding obligations. No numerical distinguishing
advantage follows from this chord theorem alone.
