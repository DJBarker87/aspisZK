# PRV campaign briefs (ready to paste)

Each brief is self-contained for `codex exec`. The lead assigns a three-letter prefix before launch. The placeholders below are `<P0>` to `<P6x>`; check the prefix registry before using any of them. Model column: terra = gpt-6.1-terra (mechanical work), sol = gpt-6.1-sol medium (proof design and semantic cases). The partition these briefs work from is `evidence/prov-plan-20261108/PRV_PARTITION.json`, and the rationale is in `PRV_REPORT.md` in the same directory.

Order and dependencies: P0 first. P1 and P5 start after P0's pilot passes. P2 starts as each P1 batch lands. P3 takes P2's failure lists. P4 runs in parallel from P0. P6 runs last.

---

## Common preamble (prepend to every brief)

```
You are a Codex worker on the Aspis R1 spend-path soundness programme (Stream A), lead note (bk) and its addendum in
docs/research/100bit-spend-path-20261013/design/C3-BIN-20261021.md. Read AGENTS.md first; its resource policy and proof
workflow bind you. Frozen source: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 (crates/, programs/r1-cost-probe, Cargo.lock);
Pool b936275465600469312d1f058cdc91ea2a11f3dc. Never edit shipped source, ledger rows, trust rows or the security contract.
Never push. Commit with plain messages and no AI trailer. Work only in your own sparse worktree and your own host workspace
under /home/dombarker/project-offloads/codex-<branch>/. Never touch another worktree, a shared launcher or index.lock.

Host discipline: every host process runs in its own systemd scope via the existing admission/launcher pattern (copy NNK_'s
batch/launcher shape from evidence/ledger27-20261111/NNK_batch.py; admission JSON with allowed:true is required before launch).
Extraction scopes: MemoryHigh=3G MemoryMax=4G MemorySwapMax=0 tasks 64, timeout 180 s. Lean scopes: MemoryHigh=6G MemoryMax=8G
MemorySwapMax=0, lean -M7000. At most 6 codex-* scopes host-wide (count all of them before admitting); host free >= 40 GB;
total reservation <= 55 GiB. A scope killed by memory or timeout is never rerun unchanged: change the shape and record why.
Two failures of the same shape class stop that shape. Every scope records target, command, source revision, exit, wall time,
peak RSS, swaps and (for Lean) #print axioms lines in <PFX>_ATTEMPTS.jsonl plus a per-scope receipt.

Reuse the retained gate export: prepend /home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNK_20261111/NNK_exports_final_20261111
to the Lean path and import NNK_COMBINED_IMPORT. Do not rebuild the gate. Read-only use of other jobs' objects; never delete
anything on the host.

Discretion (rulings as principles): where the brief's literal text does not cover a case, classify it under these
principles, record the classification and reason in <PFX>_CLASSIFICATIONS.json, and continue. Stop only for a trust-row,
security-contract or frozen-source change. No file over 20 MB in the repository (xz plus an uncompressed SHA sidecar).
Final message: exact claims with file references, what ran (scopes, wall, RSS), what remains, "Target not yet established".
```

---

## P0: tooling, regenerated partition, pilot (sol, 1 job)

```
Job <P0>_. Branch codex/cx-<p0>-<date>; evidence dir evidence/prov-campaign0-<date>/.
Inputs: evidence/prov-plan-20261108/PRV_PARTITION.json, PRV_REPORT.md, PRV_scripts/*.py;
evidence/extract-stage-20261106/NHR_stage.py (hash-pinned extractor) and evidence/emission-repro-20261110/NMH_extract.py
(spec-driven controller over the unchanged NHR extractor; reuse this pattern, do not fork NHR_stage.py).

1. Recompute the partition at your base revision with PRV_scripts (adapt paths only). Fresh receipted extractions merged
   after f7ccfbace7a move definitions from UNCOVERED to covered; record the delta. Output <P0>_PARTITION.json in the same
   schema.
2. Write <P0>_extract_specs.json: for every (c) c2 module, (b) b2 module and the cut-crate items, one or more extraction
   specs {crate, manifest path at the frozen revision, start_from roots, include/opaque lists, features}. Group by frozen
   crate and source module (expect about 35 frozen selections, about 10 cut-crate and about 8 reference configurations).
   Each spec names the committed modules and Lean definitions it is meant to cover. Cut-crate items with no frozen counterpart get
   spec kind "cut" and are routed to P4.
3. Write <P0>_gen_equalities.py: given a fresh emission output dir and a committed gate module M, emit
   PRVEq_<M>.lean that (a) contains the fresh emission renamed to namespace PRVFresh_<M> by a deterministic, recorded
   substitution list (as NHR_parameterize.py does), compiled against the committed Types module when the Types text is
   identical after normalization (otherwise against the fresh Types plus a generated structure isomorphism), and
   (b) for each reached definition in PRV_PARTITION (callee-first order) states theorem PRVEq.<M>.<f> : PRVFresh_<M>.f = <M>.f
   (or the transported form) and tries, in order: rfl; unfold both sides and rewrite with callee equalities; leave
   `sorry`-free FAILED markers for P3 (the file must still compile: failed definitions are emitted as commented
   obligations with their exact statements, never as sorry or axiom).
4. Pilot, focused only (AGENTS 4): three modules: AspisR1WideToBytesSource.Funs (a_identical; expect all rfl),
   AdapterRwTypes (c1; one differing definition), NFG_CheckedFieldRef.Funs (c2 field arithmetic; exercises the M31.add
   U32 class from NML_DiffArithmetic.lean). Run their extractions (at most 4 extraction scopes) and compile the three
   PRVEq files (at most 6 Lean scopes). Record per definition: rfl / unfold / transport-needed / semantic.
5. Calibrate: report observed rfl rate versus PRV's estimate (about 63% overall), and any reason the rename-into-shared-Types
   approach fails (for example partial_fixpoint/loop definitions not unfolding). If rfl fails systematically for loop
   definitions, add an equation-lemma congruence strategy to the generator and re-pilot once.
Deliverables: <P0>_PARTITION.json, <P0>_extract_specs.json, <P0>_gen_equalities.py (+ tests on the three pilots),
<P0>_PILOT.json, <P0>_HANDOFF.md. Budget: 15 scopes total.
```

---

## P1a / P1b: fresh frozen extractions (terra, 2 jobs in parallel)

```
Job <P1a>_ (P1b identical with the other half). Branch codex/cx-<p1a>-<date>; evidence dir evidence/prov-extract-a-<date>/.
Input: <P0>_extract_specs.json (P1a takes crates aspis-core and aspis-statement; P1b takes aspis-r1-cost-probe,
programs/r1-cost-probe and the probe/cut-crate selections that map to frozen functions).
For each spec, in order, run one extraction scope through the P0 controller (NMH_extract.py pattern over unchanged
NHR_stage.py). Reuse one Charon LLBC per crate when the spec allows it; record the LLBC hash. Each successful run commits:
raw Funs/Types/External templates, <PFX>_Ennn_PINS.json (tool binaries and hashes, full command, frozen source tree hash,
Cargo.lock hash, opacity file hash, output hashes), stdout/time logs (xz). This is the receipt that (bk) requires: the
command, pins and source hash must be complete enough that a stranger can rerun it.
Failure handling: Charon timeout or Aeneas exit != 0 -> record, then change the selection (split start_from roots, add
opaque for the failing callee and note it) and retry once; a second failure of the same shape goes to the failure list
with the exact error. Do not raise the 180 s timeout or memory caps.
Do not write Lean proofs. After each batch of 10 runs, push nothing, commit, and write <PFX>_COVERAGE.json mapping each
committed gate definition named in the specs to the fresh emission definition that covers it (or MISSING with reason).
Expected size: about 26-33 runs per job, 2-3 minutes each. Stop when every spec is either covered or on the failure list.
Deliverables: emitted outputs + PINS per run, <PFX>_COVERAGE.json, <PFX>_FAILURES.json, <PFX>_HANDOFF.md.
```

---

## P2a to P2d: generated equality modules (terra, 4 jobs)

```
Job <P2x>_. Branch codex/cx-<p2x>-<date>; evidence dir evidence/prov-eq-<x>-<date>/.
Module clusters (from PRV_PARTITION.json, recomputed by P0):
  P2a: hub cluster: RPz7_FIo_NativeTypes/Funs, FIo_QRaw*, AspisR1CanonicalQRawUnified.*, RPz7_FIp_*, AspisR1CurrentWide.*,
       CurrentWideMulCanonical, CurrentWideEqSemanticV7, S1M31EmbeddingSourceV1, Stage2ContinuationTypes, AdapterRwTypes.
  P2b: RPu_FIq_* (14 parts + NativeTypes/External/CopyPrefix), RPv_* slices.
  P2c: aspis-statement / Pool-terminal family: AspisR1TerminalDecoder.*, NFY_Part042/043, Port23PUSH_Source,
       AspisR1PublicPreparation.*, AspisR1AdapterReconstruct.*.
  P2d: everything else in c1/c2 (field/sampler/parser/caller-model modules).
For each module in your cluster whose fresh emission exists (P1 COVERAGE says covered):
  1. Run <P0>_gen_equalities.py to produce PRVEq_<M>.lean.
  2. Compile it as one focused Lean scope (AGENTS rule 1: smallest file first). Never compile the gate.
  3. Record per definition: PROVED_RFL, PROVED_UNFOLD, or FAILED(statement, first failing goal, diff of normalized
     text). Run #print axioms on every proved theorem; only propext, Classical.choice, Quot.sound are acceptable.
  4. Do not hand-edit generated proofs beyond what the generator's documented strategies do. Do not add simp sets,
     norm_num or decide on large terms (AGENTS 2/3). A failure is data for P3, not something to force.
Deliverables per module: PRVEq_<M>.lean, its receipt and axioms output; cluster-level <PFX>_EQ_STATUS.json listing every
reached definition with its status; <PFX>_FOR_P3.json (FAILED definitions with goals and normalized diffs).
Expected: about 30 modules per job, one scope each (2-6 minutes), about 60% of definitions proved by rfl/unfold.
```

---

## P3a to P3d: differing definitions (sol, 4 jobs, one per P2 cluster)

```
Job <P3x>_. Branch codex/cx-<p3x>-<date>; evidence dir evidence/prov-eqproof-<x>-<date>/.
Input: <P2x>_FOR_P3.json, the PRVEq_<M>.lean files, NML_DIFFS_CLASSIFIED.json and NML_DiffArithmetic.lean (template for
the semantic M31.add class), NND_PROVENANCE.md (require_zero historical index loop versus frozen suffix loop).
For each FAILED definition classify first, then prove:
  NOMINAL: differences are namespaces, explicit opaque-call parameters, imports or discriminant metadata. Write one
    per-module transport (structure isomorphism or parameter instantiation) and prove the equality through it. Prefer
    one generic lemma per module over per-definition proofs.
  SOURCE_SHAPE: different but equivalent control flow (require_zero class). Prove full equality by a loop
    invariant or fuel induction; state it for all inputs.
  SEMANTIC: the bodies disagree on some inputs (M31.add on non-canonical U32). Prove equality on the domain the CLOSED
    callers establish, and prove (or cite by theorem name) that every reaching CLOSED root's use stays in that domain.
    If a caller domain cannot be shown, stop that definition and report it with the counterexample input: that is
    a finding against the affected rows, never something to hide by narrowing a statement.
Rules: no axiom, no sorry, no trust-row additions. Do not restate a CLOSED root. Focused compiles only. #print axioms on
every new theorem. Two failed proof shapes on one definition -> stop it, record both, move on.
Deliverables: proved PRVEq_<M>_P3.lean files, <PFX>_CLASSIFICATION.json (NOMINAL/SOURCE_SHAPE/SEMANTIC per definition),
<PFX>_REMAINING.json, handoff. Expected total across P3: about 370 definitions, of which about 320 NOMINAL and about 25-45
SOURCE_SHAPE/SEMANTIC.
```

---

## P4a / P4b: reference and cut-crate lane (terra; b3 escalates to the lead)

```
Job <P4x>_. Branch codex/cx-<p4x>-<date>; evidence dir evidence/prov-ref-<x>-<date>/.
Scope: PRV_PARTITION modules with subgroup b2/b3 (20 modules; P4a: neg_isolated family NFS_AccumPart00,
NEV_AccumulateRaw.*, NEI_PushRaw.*, plus NHI_*, NGD_AtG.Types, NGM_GuardRef.Funs, NHJ_SnapshotReference.Types;
P4b: Multiproof{Cone,Sort,Parser}Ref.*, NHV_NE{B,O}_* refs) and the 15 c modules with cut-crate items
(WAdm_model, values_owned_reference, check_values_owned, copy_chunk, encode_digest_canonical, canonical::raw ...).
1. Locate the reference or cut-crate Rust source. Search the whole research tree (not only the job dir) and the LLBC
   containers (item_meta.source_text embeds source; see NML_INPUT_MAP.json 'embedded'). A source counts only if
   its bytes hash-match an LLBC/receipt record or reproduce the live module on re-extraction.
2. If found: commit it under evidence/prov-ref-<x>-<date>/sources/ with its sha256, re-extract with a fully recorded
   configuration (same receipt standard as P1), and generate equalities to the live gate module with
   <P0>_gen_equalities.py. Then confirm that the Kani contract tying the reference to the frozen function names this exact
   source hash (cite harness and receipt). If the Kani receipt names a different hash, report it; do not rerun Kani in
   this job.
3. If not found after the full search: stop that module and write a lead decision packet with two options and their
   cost: (R) reconstruct the reference from the Kani harness's recorded contract and re-run that Kani harness;
   (F) re-route the consuming bridge to a P1 frozen emission. Do not choose; the lead decides.
Deliverables: located/committed sources with hashes, receipts, PRVEq files, <PFX>_DECISIONS_NEEDED.md.
```

---

## P5: a lane (terra, 1 job)

```
Job <P5>_. Branch codex/cx-<p5>-<date>; evidence dir evidence/prov-a-<date>/.
Scope: PRV_PARTITION a_identical (20 modules) and a_pending (19 modules).
a_identical: the reached definitions are text-identical to an existing fresh frozen receipted emission. Generate
  PRVEq_<M>.lean against that existing emission (no new extraction) and compile; expect PROVED_RFL throughout. Any
  failure moves the module to the P3 queue with the goal recorded.
a_pending: the module's live version is either a receipted emission or a retained copy (parameterized output or
  older version). Prove constant-level equality between the gate constant and the receipted emission's definitions
  (same generator). Where the retained copy was produced by a recorded deterministic generator (NHR_parameterize.py,
  NNG/NMP syntax parameterization; see NNK_SYNTAX_ASSOCIATION.json), rerun that generator on the receipted output and
  record byte equality to the committed copy as additional evidence. AdapterRwModel: also cite NND's equality theorems
  for the TX2 definitions and the require_zero case; do not duplicate them.
Deliverables: PRVEq files, per-module status, handoff. Budget about 45 Lean scopes.
```

---

## P6: composition and provenance line (terra, 1 job)

```
Job <P6>_. Branch codex/cx-<p6>-<date>; evidence dir evidence/prov-compose-<date>/.
1. Build one combined import of all PRVEq_* modules from P2-P5 on top of the gate export (no gate rebuild), compile it, and
   run #print axioms on every PRVEq theorem in one audit pass (standard axioms only).
2. Produce <P6>_PROVENANCE.json: for every emitted gate module reached by a CLOSED root, its status:
   RECEIPTED (receipt path), EQUALITY_PROVED (fresh receipt + theorem names), EQUALITY_DOMAIN (semantic class, with the
   caller-domain theorems), or OPEN (reason). Then per CLOSED row: provenance-clean or conditional, with the OPEN modules
   it depends on (same reliance method as PRV_PARTITION).
3. Write the provenance status line for the next ledger in the form ledgers 25-27 used, with the new counts.
   Do not edit ledger rows; the ledger job consumes your JSON.
Release replay, L187/L188 and source-to-ELF are out of scope; say so.
```
