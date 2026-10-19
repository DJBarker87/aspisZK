# check_sound⁗ import budget (D66 follow-up, branch codex/r1p-checker-wrapper-20261019)

Job: make the pb/ct-level wrapper `check_sound''''` (source of attempts 4615/4616,
`c3/evidence/lean/CertCheckSound5-4616.lean.txt`) compile under -M7000 / MemoryMax 7G.

## 1. Measurement (read-only, host, 2026-10-19 ~09:45 London)

Tool: `importsize.py` (this directory). It follows `import` lines from the sources tree,
the package sources and three extra source roots for the 17 modules whose sources are
not in the workspace tree (Aeneas, Wide, AspisV8R19; 3 AspisV8R19 leaves remain unfollowed,
so closures are lower bounds by at most those leaves). Sizes are `.olean` bytes resolved
in the launcher's order (objects dir first, then LEAN_PATH).

Workspace A (`aspis-fs-generic-20261006`, objects2 + environment-base), where
CertCheckSound2–4 and CertRel* were built:

| import set | modules | olean GB | observed peak RSS |
|---|---|---|---|
| R1Z.CertData | 2,495 | 0.516 | 1.95 GB (4369) |
| R1Z.CertCheckExtracted (Aeneas.Std) | 3,838 | 0.738 | 2.62 GB (4363, Base) |
| R1Z.CertRelFill | 5,416 | 1.190 | 3.83 GB (4610) |
| Mathlib (whole) | 10,316 | 2.170 | – |
| R1Z.PredicateR1 | 10,604 | 2.375 | – |
| R1Z.CertCheckSoundRel imports | 10,626 | 2.391 | 6.81 GB (4617) |
| R1Z.CertCheckSound4 imports | 11,385 | 2.528 | 7.19 GB (4512) |
| wrapper imports (Sound4, CertRelFill, CertRelData) | 11,394 | 2.537 | 7.18 GB at kill (4615/4616) |
| **floor**: PredicateR1 + Cert{Check,Build,Rel}Extracted only | 11,340 | 2.498 | ≈7.1 GB (fit) |

Peak RSS is close to linear in the closure's olean bytes (≈ 0.6 GB + 2.6 × olean GB).

Where the bytes come from (wrapper closure): Mathlib 1.81 GB of 8,265 modules, i.e.
**all of Mathlib**; Lean core 0.30 GB; every project module together < 0.2 GB. Whole
Mathlib enters through `import Mathlib` in base modules, not in any R1Z module:
AspisFormal.CircleGroupOrder (needed for `AspisCircleGroupOrder.P` in every statement),
CircleFibreRoots, CircleNaturalBasis, CircleDiscreteAvailability, CirclePointLiveness,
CircleRectangularMasking, SoundnessLedger, V5ComponentCConcreteFoldLinearity, V5FriBitReverse,
V5FriJohnsonListBound, V5FriListCap, V5FunctionalBatching, V5WithoutReplacementQuerySoundness,
R0P.MessageDescent, R0Z.GoodDensity, R0Z.StatisticalDistance. Any module that states `P_R1`
therefore loads all of Mathlib in workspace A.

The Aeneas side adds 732 modules / 0.119 GB on top of PredicateR1 (Aeneas.Std 36 MB,
Aeneas.Tactic 20 MB, AeneasMeta 17 MB, Lean.Meta/Compiler/Elab 26 MB).

Consequence: the wrapper's statement mentions both `P_R1` and the extracted `check`/`fill_*`,
so its closure is at least the floor (2.498 GB). The whole R1Z checker chain (Sound2–4,
CertOwn*, CertRel*) adds only 0.039 GB olean (≈0.1 GB RSS) above the floor. **No split of
CertCheckSound2–4 into statement/proof modules can bring the wrapper comfortably under 7 G
in workspace A**: the floor itself loads at ≈7.1 GB against a 7.168 GB (7000 MiB) -M limit.

Unified env J (`aspis-joint-20261019`, LOG D65/D67), where the base files import bounded
Mathlib sets: R1Z.PredicateR1 closure 4,775 modules / 1.253 GB; CertCheckSound3 closure
5,888 / 1.446 GB, no whole-Mathlib importer. Predicted wrapper load ≈ 4.5 GB.

## 2. What was done instead of splitting Sound2–4

The refactor the job proposed (statement/proof split of CertCheckSound2–4, light interface
modules, no Aeneas import at the composing level) cannot work in workspace A. The measurement
shows the wrapper's floor is set by its own statement (`check pb ct = ok true` and the `fill_*`
runs on one side, `P_R1` on the other), and that floor is ≈7.1 GB. The `import Mathlib` that
has to be narrowed is in the base, and env J already narrows it. So the chain was carried over
to J unchanged, and the wrapper was compiled there. No accepted statement changed and no module
was split or moved. The only new source is `lean/R1Z/CertCheckSound5.lean`: the 4616 wrapper
with two proof-only fixes. 4615/4616 never got past import, so the proof had never been checked:
- `dsimp only [coefK] at hent` made no progress (5647). `coefK` is an abbrev applied
  partially, and the line is removed.
- The width argument stayed `nfU` inside `coefK` while `rel_data` expects `nf` (5648). The
  fix is `subst hnfU` before the rewrite.

## 3. Env-J attempts 5600–5649, 5700 (`evidence-j-5600-5700.jsonl`)

Driver: `jrun.py` calls run-joint.sh directly, one module per attempt, with no extra lock.
The fingerprint follows joint-drive.py: manifest imports for manifest modules. For new modules
it is the transitive project closure, so that an indirect change, such as the re-extracted
CertBuildExtracted, counts as a new input. Before each build, a guard checks the J source sha
and checks the sent log for a newer different source from another worker.

- **5600–5621**: rebuilt the 22 manifest-3 modules that were stale after the D67 narrowing
  (RfChain … CertCheckSound3). Sources unchanged, all green, peak ≤ 4.10 GB, standard axioms.
  Pre-rebuild objects: `snapshot-J-pre5600-olean.sha256` (copies on the host under
  `codex-r1p-checker-wrapper-20261019/snapshot-J-objects/`).
- **5622**: CertOwnFill failed: unknown `R1CertBuild.own_c1`/`fill_own`. J's
  `R1Z.CertBuildExtracted` was the pre-D62 extraction (sha 27f2dc76…, manifest-3), and the
  repo/D62 copy is d7e06b9f… (the D62 diff only adds declarations). **Shared source and
  olean overwritten** (lead-approved): J/sources/R1Z/CertBuildExtracted.lean ← repo copy.
  The old source and the 17 objects are snapshotted at
  `snapshot-J-pre-certbuildextracted/` (`snapshot-J-pre-certbuildextracted.sha256`).
- **5623–5632**: rebuilt CertBuildExtracted and its dependents, all green.
  CertBuildIdent2, CertCheckSound2, CertLiftIdent–4 and CertCheckSound3 were *refused* by
  run-joint.sh (exit 67, no attempt consumed): same source and byte-identical dependency
  objects. Their existing objects are therefore built from identical inputs. joint-drive.py's
  attempt-order `stale()` still flags CertBuildIdent2 and CertLiftIdent, and manifest-3 still
  carries the old CertBuildExtracted sha. Manifest-3 needs CertBuildExtracted's sha updated
  to d7e06b9f…, or the driver will try to rebuild.
- **5633–5646**: new modules CertOwnFill, CertOwnIdent, CertOwnEntries, CertOwnBlock,
  CertCheckSound4, CertRelExtracted, CertRelW, CertRelK, CertRelWeights, CertRelCoef,
  CertRelFill, CertRelIdent, CertRelWId and CertRelData were built with sources byte-identical
  to the repo/D64/D66 copies. All green, peak ≤ 4.11 GB.
- **5647, 5648**: the wrapper failed on the proof errors above.
  **5649: `R1Z.CertCheckSound5` green, peak RSS 4,128,696 KiB (≈4.13 GB, ≈3.0 GB under
  the cap), 2.39 s, 0 swaps.** `#print axioms check_sound''''`: [propext, Classical.choice,
  Quot.sound]. Object sha256 fe5e50bc…bc66.
- **5700**: `CertCheckSoundRel` (`p_r1_of_data_rel`) in J, green, 3.61 GB, standard axioms.

Note: the `axioms` field that jrun.py wrote at build time missed names containing `'`.
The committed JSONL carries axioms re-parsed from the out logs, marked `axioms_source`. The
records jrun.py appended to J/evidence/attempts.jsonl keep the build-time field.

## 4. Named premises left in `check_sound''''` (statement as in 4616, unchanged)

- Builder identifications: `hRound`, `hGRound`, `hGBat` (another worker owns these).
- Decoder facts: `hup`, `hnq`, `hz`, `hrw`.
- Chain builder: `hT` (Tower), `hal`, `ha9`, `hbuild` (fill_tq run).
- BCondG: `wb`, `fp`, `hcov`, `hbw`, `sel`.
- Lift: `hnl`, `hsel1`, `hlw1`, `hselH`, `hlwH`, `hnqU`, `hzx`, `hzy`, `htr`, `hin`, `hsx`, `hsy`,
  `hselC`, `hselHv`, `hloC`, `hloH`, `hblo` (fill_lo run).
- Own: `hnU`, `hosU`, `hos`, `hbo`, `hrow`, `hlimbB`, `hlane`, `hwl`, `hgnU`, `hgwU`, `hgw`, `hbg`,
  `hgk`, `hselG`, `hgrow`, `hglane`, `hgwl`.
- Relation (D66): `hW` (w·w = B.u), `hwb` (limb basis), `hnfU`, `hqU`, `hbr` (fill_rel run),
  `hti` (ti = π⁻¹), `hop` (openings), `hfp`, `hinj` (fp injective), `hru`, `hrq` (query
  bounds), `hl0`–`hl2` (li = lineInverse), `hx16` (x16 = storedLine16X).

hRel, hOwn, hGOwn, hChain, hhalf, hC1 and hH1 are discharged.

Module paths for importers: in env J, `R1Z.CertCheckSound4`, `R1Z.CertCheckSound5`
(`check_sound''''`), `R1Z.CertCheckSoundRel`, `R1Z.CertRel*` and `R1Z.CertOwn*` are now in
`aspis-joint-20261019/sources/R1Z` and `objects/R1Z`. No module moved in the repo.
