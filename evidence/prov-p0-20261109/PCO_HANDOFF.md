# PCO_ HANDOFF: phase P0 of the (bk) extraction-provenance campaign

Target not yet established. This job changes no ledger row, trust row, RSL, security contract or shipped source. A definition without a proved equality keeps its rows conditional for the release claim.

Branch `codex/pc-prov-p0-20261109`, base research `6ce07a6a593` (ledger30 gate). Frozen source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Host workspace `/home/dombarker/project-offloads/codex-pc-prov-p0-20261109/`.

## 1. Claims established, with references

1. **The PRV partition method is reproduced.** `PCO_partition.py` (a port of PRV_scripts) run at f7ccfbace7a on the ledger27 gate reproduces PRV_PARTITION.json exactly: module groups and subgroups, blob groups, rows 553/532/538, definition coverage 145/92/172/473/119. Only the informational `c_modules_uncovered_not_frozen_mappable` differs (5 vs 15). `PCO_CONTROL.json`, substitutions S1-S7 in `PCO_CLASSIFICATIONS.json`.
2. **Partition at the new base** (`PCO_PARTITION.json`, same schema as PRV plus `pilot_correction`, `shadow_candidates`, `compiled_source_ambiguous`). 599 CLOSED rows, 1099 roots, 373 emitted gate modules (+3: NMT_first.Funs/.Types, NMT_tx1.Funs). Rows relying on a group (c) module: **544 of 599 (PRV: 532 of 587)**; on c or b2/b3: **550 (PRV: 538)**; on any non-receipted emitted module: 565 (PRV 553). All 12 added rows are the ledger30 instantiations (TX1:094, 328, 330, 333, 344, 345; TX2:213, 221, 233, 240, 241, 242); none left group c. Module groups: R 70, c 127 (c1 42, c2 75, c0 10), a 41 (a_identical 19, a_pending 22), b 20, d 115. `PCO_PARTITION_DELTA.json` lists every change with its reason: 3 new fresh frozen emission files (NMX_auth_box, tx2-auth-20261111), 6 regrouped modules (NMT_stage1_owned.Funs/.Types and NMT_tx1.Types now reached; NNG_verify_finish.Funs/.Types gained receipts; one pilot correction), 181 modules with changed row counts only.
3. **One PRV classification was wrong, and the cause is general.** AspisR1WideToBytesSource.Funs was a_identical; the compiled gate module is the hand-adapted `generated-adapted/Funs.lean` (three lines replace the Aeneas iterator/zip externals by P6ToBytes.StdModel), which PRV could not find because its path does not name the module. Proof: the self-copy control PCO_L007 (adapted text as a fresh emission: 8/8 rfl against the gate) and PCO_L008 (the fresh frozen emission matches only to_limbs). Moved a -> c1. `PCO_shadow.py` finds 14 modules (2 a_identical, 3 c1, 7 c2, 1 c0, 1 receipted) with a second same-import, same-namespace blob; they are flagged `compiled_source_ambiguous` and their PRV group is provisional. The equality statements are against compiled constants, so they are unaffected.
4. **Extraction specs** (`PCO_extract_specs.json`, built by `PCO_make_specs.py`): 4 pilot specs (S900-S903, S902 retired), 17 runnable frozen selections plus 9 types-only selections (roots to be taken from the callers; field `roots_needed`), 17 `cut` entries (routed to P4), 17 `reference` entries (P4), 10 unmapped c0 modules. P1a = aspis-core and aspis-statement (13 selections); P1b = probe, program, pool and cut-mapped items (9). The count is below the plan's ~35 frozen selections because only UNCOVERED/COVERED_DIFFERS definitions of c2 modules produce roots and no opacity splits are guessed; the include/opaque lists are empty and must be filled from the matching NMH/NMS/NMT specs, as S903 was.
5. **Pilot** (`PCO_PILOT.json`):
   - AspisR1WideToBytesSource.Funs (E001, L008): 7 common declarations, 3 rfl (two instances and to_limbs), 4 transport-needed (the ChunksExactMut instance and the three loop/bytes functions): fresh declarations do not elaborate against the gate's external model.
   - NFG_CheckedFieldRef.Funs (E002, L009): 7 declarations: 3 rfl (the is_zero chain), 1 unfold (`field.P`, irreducible), 3 semantic: `M31.neg` (checked `field.P - self` in the gate, `wrapping_sub` in the frozen source: equal on canonical self <= P only, the M31.add U32 class) and the text-identical `CM31.neg`, `QM31.neg` blocked by it.
   - AdapterRwTypes (E003 retired, E004, L006): 14 Lean statements, all rfl (10 rfl equalities incl. M31, SolanaDigest and the 8 closure unit types, 3 generated Equivs); of the 15 reached types 10 are Lean-proved, 4 structures are text-identical only, and the one differing definition is `solana_pubkey.Pubkey`: an external axiom in the fresh emission, `Array U8 32` in the gate (inherited SDK-model assumption, not proved).
6. **Calibration.** Funs lane over the 8 reached definitions of the two Funs pilots: 1 rfl, 1 unfold, 6 not equal. PRV's text identity predicted 5 identical of 8. Three causes (PCO_CLASSIFICATIONS PILOT-1/2/6): wrong compiled candidate; identical text with a non-equal callee; hand-written external models in the gate. n = 3 hand-picked modules, so this calibrates causes, not the 63% population rate. **Loops are not a problem**: `loop (fun ..) ..` definitions and loop bodies are closed by plain `rfl` in the control; no equation-lemma strategy was added and no re-pilot was triggered.

## 2. What ran (all receipts in this directory)

| scope | target | exit | wall s | peak RSS KiB |
|---|---|---|---|---|
| PCO_E001 | S900 aspis-core r0, `field::wide_exact::_::to_le_bytes` | 0 | 22.9 | 726332 |
| PCO_E002 | S901 aspis-core r0, `field::_::neg`, `field::_::is_zero` | 0 | 22.3 | 725196 |
| PCO_E003 | S902 program crate, NMH_E002 entry array (retired: only ProgramError emitted) | 0 | 113.9 | 539744 |
| PCO_E004 | S903 program crate, four owned roots, merged opaque list | 0 | 73.5 | 649264 |
| PCO_L001 | WTB probe (unnamed trace markers: stage not recoverable) | 1 | 2.3 | 2627140 |
| PCO_L002 | WTB probe | 1 (expected: fresh errors) | 2.2 | 2632304 |
| PCO_L003 | bundle NFG + AdapterRwTypes probe (`discriminant isize` parse error in fresh Types) | 1 | 3.3 | 2689108 |
| PCO_L004 | bundle final candidates (unterminated nested comment) | 1 | 2.0 | 2621076 |
| PCO_L005 | bundle WTB + NFG final + AdapterRwTypes obligations-only | 0 | 3.1 | 2712964 |
| PCO_L006 | PRVEq_AdapterRwTypes (final) | 0 | 3.1 | 2694296 |
| PCO_L007 | PRVEq_control_WTB (self-copy control) | 0 | 2.2 | 2645760 |
| PCO_L008 | PRVEq_AspisR1WideToBytesSource_Funs (final) | 0 | 2.0 | 2637316 |
| PCO_L009 | PRVEq_NFG_CheckedFieldRef_Funs (final) | 0 | 2.1 | 2634584 |

13 of 15 scopes; extraction caps 3G/4G, Lean 6G/8G, swap 0, tasks 64, timeout 180 s; swaps 0 everywhere; each admission had host scopes < 6, Stream C scopes < 3, disk >= 40 GB, allowed:true (`PCO_*-admission.json`, `PCO_*-disk-*.json`). No memory kill, no timeout, no cap raised. Source revision of each scope is in `PCO_ATTEMPTS.jsonl` (HEAD at launch; dirty flag recorded). `#print axioms` of every final theorem: propext, Classical.choice, Quot.sound only (the receipts' `print_axioms`); no sorry, no axiom declaration, no native_decide, no raised maxHeartbeats beyond the Aeneas header values copied from the fresh emission. The probe receipts L001-L004 contain sorryAx in axiom lines because failed theorems were elaborated with error recovery; they are probe artefacts and none of those files is a deliverable.

Extraction receipts: `PCO_E00n_emitted/` (raw Funs/Types/External templates, `PCO_E00n_PINS.json` with tool hashes, full commands, frozen tree hash d461fbc56cec8ba29678d6613fc38e6c795d6a66, Cargo.lock hash, spec (= opacity file) hash, output hashes; `PCO_OPAQUE_CHECK.json`; xz logs) and `PCO_E00n/receipt.json`.

## 3. Deliverables

`PCO_PARTITION.json`, `PCO_PARTITION_DELTA.json`, `PCO_CONTROL.json`, `PCO_extract_specs.json`, `PCO_gen_equalities.py` (+ `PCO_gen_equalities_test.py`, offline, three pilots, ALL PASS), `PCO_PILOT.json`, `PCO_ATTEMPTS.jsonl`, `PCO_CLASSIFICATIONS.json`, this file; tools `PCO_partition.py`, `PCO_partition_delta.py`, `PCO_finalize_partition.py`, `PCO_shadow.py`, `PCO_make_specs.py`, `PCO_render_spec.py`, `PCO_extract.py`, `PCO_run.py`, `PCO_run_host.py`, `PCO_bundle.py`, `PCO_pilot_report.py`; generated modules `PRVEq_*.lean` (finals: the three named files; `PRVEq_control_WTB.lean` is the control; `PRVEq_bundle_pilotB*.lean` are compile vehicles); `pilot/` (gate source copies with SHA256SUMS, per-round reports, states and Lean logs).

## 4. Exact command lines for P1, P2, P5

Copy `PCO_extract.py PCO_run.py PCO_run_host.py PCO_render_spec.py PCO_STAGER_PIN.json PCO_extract_specs.json PCO_gen_equalities.py PCO_bundle.py` and `PCO_partition.py` next to each other in the job's `evidence/<job>/` directory (they resolve `../extract-stage-20261106`, `../emission-repro-20261110` and `../ledger30-20261111` relative to that directory, so those must be in the worktree's sparse set). Set the job's own host workspace: `export PCO_HOST_BASE=/home/dombarker/project-offloads/codex-<branch-with-dashes>/`. The run attempt ids are `PCO_E###` and `PCO_L###` (rename the prefix per job in the regex of PCO_run.py line 21 and the file names, or keep the PCO_ prefix inside the job's own directory). One scope at a time per job.

**P1 (fresh frozen extractions), per spec:**
```
python3 PCO_render_spec.py S013 PCO_E013            # writes PCO_E013_spec.json; kind must be `frozen`
# review/fill include and opaque lists in PCO_extract_specs.json for roots_needed or deep callees first
python3 PCO_run.py PCO_E013 extract                 # admission, upload, 3G/4G scope, collection, receipt
```
The receipt is `PCO_E013/receipt.json`; the pins are `PCO_E013_emitted/PCO_E013_PINS.json`; raw output `PCO_E013_emitted/raw/<namespace>/`. A cold program-crate build took 114 s here, inside the 180 s timeout; a timeout is recorded, never raised.

**P2 (equality modules), per gate module M:**
```
python3 PCO_gen_equalities.py --partition PCO_PARTITION.json --module M --fresh-dir PCO_E013_emitted/raw/<ns> --fresh-ns <ns> \
  --gate-source <compiled source text of M> [--gate-types-source <compiled Types source>] \
  --out PRVEq_<M with . -> _>.lean --report PRVEq_<M>.report.json --state PRVEq_<M>.state1.json
python3 PCO_run.py PCO_L001 lean PRVEq_<M with . -> _>          # probe; stdout.log.xz holds the Lean log
xz -dc PCO_L001/stdout.log.xz > probe1.log
python3 PCO_gen_equalities.py <same args> --state PRVEq_<M>.state1.json --state-out PRVEq_<M>.state2.json --lean-log probe1.log
python3 PCO_run.py PCO_L002 lean PRVEq_<M with . -> _>          # verify: final if exit 0
```
Several modules in one scope: `python3 PCO_bundle.py PRVEq_bundle_X.lean offsets.json PRVEq_A.lean PRVEq_B.lean`, compile the bundle, and ingest its log with `--bundle-offsets offsets.json`. Never pass the same file as `--state` and `--state-out`. The report lists per definition rfl / unfold / transport-needed / semantic, `fresh_dropped`, `names_resolved_to_gate_funs`, `external_funs`/`external_types`, `types_identity`. The first compile of an unseen module is expected to report failures; that is the information.

**P5 (a lane):** a_identical and a_pending modules go through the same two commands. The compiled text of a module with `compiled_source_ambiguous` must be fixed first: build a self-copy control (`pilot/control_wtb/` shows the shape: the candidate text with its namespace renamed as the "fresh" directory) and require 100% rfl against the gate; a candidate that fails is not the compiled source. The statements themselves are against the gate constants either way.

**Partition rerun at another base:** `python3 PCO_partition.py --rev <rev> --gate-dir <ledgerNN-dir> --gate-prefix <NNx> --scratch DIR --out OUT.json` from `evidence/` (about 6 minutes), then `PCO_shadow.py DIR shadow.json <gate LOADED_scan>`, `PCO_finalize_partition.py`, `PCO_partition_delta.py`. Validate a changed method on f7ccfbace7a first.

## 5. What remains, and what is not established

- Every group (c) and (b) module still lacks its equality theorems; of the pilot's 31 Funs-lane and type statements only the listed ones are proved, and the failures (WideToBytes loop/bytes functions, M31.neg and its callers) are P3 obligations with the exact statements in the commented `PRV-OBLIGATION` blocks.
- Fresh-vs-gate comparison inherits the gate's external models: names in `external_funs`/`external_types` (e.g. `solana_pubkey.Pubkey`, `core.slice.Slice.chunks_exact_mut`) resolve to the gate constants by name. Those are assumptions of the gate modules (the retained extraction/runtime trust rows), not equalities proved here.
- Type isomorphisms are generated only for simple structures; 4 reached AdapterRwTypes structures and all inductives are text-identical only.
- The 14 shadow-candidate modules and the group of every a_pending module are provisional until their compiled source is fixed by a control.
- The reference lane (b) and the cut crates (17 entries) are not touched; the unmapped c0 modules (10) need manual mapping.
- Specs have empty include/opaque lists except the pilots; roots of the 9 types-only selections are not derived.

Next concrete deliverable: P1a and P1b run the 17 frozen selections (S001-S022 minus types-only) after filling opacity from the NMH/NMS/NMT specs; P2 runs the generator on the c1 modules first (extraction already exists), then the c2 modules.
