# FIN_: one-step instantiations of TX2:240/221/213 and TX1:333/330

Target not yet established. These five modules close no row on their own. The
ledger gate decides credit after the host build below passes.

Base: research 82495476f4f. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
RSL rev4 (evidence/rowspec-lead-20261107).

## The five roots

Each root applies one fold to the child candidate roots at the LIB_FullInstances
library (L, D, V0, VL, P, C). The 233 allocation `choices` and the 240 window
`allocation` are universally quantified, so each row holds at every allocator
interpretation. No hypothesis is added, and each conclusion is the RowSpec exactly.

| Row | Root | Fold | Children |
|---|---|---|---|
| TX2:240 | `FIN_240.candidate` | `NMV_ConcreteWindows.root240` | `NMX_R9_StageTwo.root` |
| TX2:221 | `FIN_221.candidate` | `NVR_Folds.process_tx2` | `AspisR1.NNG_Candidate344.candidate`, `FIN_240.candidate` |
| TX2:213 | `FIN_213.candidate` | `NVR_Folds.entry_tx2` | `FIN_221.candidate` |
| TX1:333 | `FIN_333.candidate` | `NVR_Folds.process_tx1` | `AspisR1.NNG_Candidate344.candidate`, `FIN_240.candidate` |
| TX1:330 | `FIN_330.candidate` | `NVR_Folds.entry_tx1` | `FIN_333.candidate` |

`FIN_COMBINED_IMPORT` checks by `rfl` that the 333 producer is the 221 producer
and that the 330 producer is the 213 producer. The rows share one function each.

RowSpec_213/330 keep (E1), Root0 on the ASQ8 route at V0, as a Domain premise.
FIN_CALLER_CLAUSES.json routes that premise to the top (G0) through NNC_ option B.
It also records the NLG-upstream resume-extent dispositions at 240/221/213, each
`discharged_by` NMX_R9_StageTwo.root (TGB-5).

## What was checked locally

Every module was compiled with a focused single-file compile, `lake env lean -o`,
on macOS with Lean 4.31.0. Only core Lean was used. The log is
shapecheck/FIN_SHAPECHECK_COMPILE.tsv: 52/52 modules exit 0, peak RSS 0.70 GB,
0 swaps. The build used these sources:
- the real RSL rev4 files, TAS_Interfaces and TCK_WeakRoot0;
- the 15 real NMV_ modules up to NMV_ConcreteWindows;
- NVR_Dispatch/NVR_Folds rebuilt locally from the research NNF_ sources by the
  rule NVR_ states. These are identical, apart from comments, to the uncommitted
  NVR_ drafts; see shapecheck/*.local.txt;
- the five FIN_ files and FIN_COMBINED_IMPORT, unchanged from this directory.

The remaining modules were replaced by SCRATCH STUBS (shapecheck/*.stub.txt):
LIB_Deployed, LIBB_PoolLib, LIBB_V2Star, LIB_Instances, LIB_FullInstances,
NMX_R9_StageTwo and NNG_Candidate344. Each stub declares the real names with
their exact signatures, and with `axiom` for the opaque values and the two child
roots. The abbreviation chain the real files use is kept, so the check depends on
the same definitional equalities, for example NMX `D := LIBB_PoolLib.deployed`
against `LIB_FullInstances.D := LIB_Instances.D`. The stubs are evidence of term
shape only and are not committed as .lean. Printed axioms in the stub run are the
stub axioms plus propext and Quot.sound.

Negative control: when NMX's `D` was replaced by an unrelated constant, FIN_240
was rejected with an application type mismatch at `NMX_R9_StageTwo.root`.

## Unchecked: exact host recipe

These items are NOT yet checked: the real NMX/NNG/LIB closures, a combined import
and a raw axioms audit.

1. Wait for NVR_ to commit NVR_Dispatch and NVR_Folds with the signatures in
   FIN_IMPORTS.json, together with rev4 objects for the NMV chain through
   NMV_ConcreteWindows.
2. **Coherence first.** The two child closures were built against different RSL
   objects. In the NMX closure, RSL_Base.olean is sha256 dd8125eb… (1,456,904 B,
   from NMS_RSL_objects; NMX_CLOSURE_PINS). In the NNG closure it is 5514b548…
   (1,593,352 B, NNG_F9_objects; NNG_R4Final_RETENTION). Do not put both on one
   LEAN_PATH. Establish which RSL source revision each object was compiled from.
   Then rebuild the side that is not rev4 against the single rev4 object set that
   NVR_ uses, before compiling FIN_. Compiling FIN_ is not the same as a coherent
   build.
3. On the NUC, use one pinned workspace and toolchain v4.32.0, the version both
   child closures used. Run each module in its own scope:
   `systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 lake env lean -j1 -M7000 -DElab.async=false -o <objdir>/<M>.olean <M>.lean`
   Compile in this order: FIN_240, FIN_221, FIN_213, FIN_333, FIN_330,
   FIN_COMBINED_IMPORT. Set LEAN_PATH to the single coherent rev4 object set plus
   the NMX, NNG, LIB and LIBB objects that were rebuilt on it. Each FIN_ module is
   a term application, so a module that needs more than about 1 GiB should be
   stopped and inspected.
4. Run the raw axioms audit on the five `candidate` theorems. The expected
   axioms are propext, Classical.choice and Quot.sound only.
5. Record the target, exit status, wall time, peak RSS, swap, source revision and
   printed axioms for every compile.

## Residuals carried into the ledger

None of these items is introduced by FIN_.
- (E1) Root0 at 213/330 is caller-owned and goes to the top. The option-B route
  needs a weak-V 241 root (TCK G1b). NMX_R9_StageTwo.root is proved at V0 only.
  It also needs the per-Env weak law (TGB-1, LIBW_).
- The 241 occurrence of NLG-upstream, including '.S2', stays with the 241 gate
  (TGB-5).
- At 240, the Clock::get BorshIoError allocation (TGB-4) is a lead decision. The
  FibreIndex::get call-domain item is a separate ledger row.
- 344/345 retain the ruling (bn) ReviewedTranscription and the existing
  SDK/std/runtime trust (NNG_REMAINING). 241 retains its own D1/D2 clauses.
