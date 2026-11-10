#!/bin/bash
# PCXE_finalize.sh: PCXE_TRUST_NAMING.json, L187 addendum, non-frozen owner status, PCXE_CLASSIFICATIONS.json, PCXE_TOOLS.json, PCXE_STATUS_LINE.md, delta section of PCXE_TRUST_PROPOSALS.md, notes in PCXE_ATTEMPTS.jsonl.
# Run after PCXE_rerun.sh. Idempotent for the JSON files; the TRUST_PROPOSALS delta and the ATTEMPTS notes are appended once (guarded).
cd /Users/dominic/ZK/.worktrees/pc-prov-p6t/evidence/prov-p6t-20261110
python3 -I -B - <<'PY'
import json, hashlib, glob, collections
N = json.load(open('PCXE_NUMBERS.json')); A = json.load(open('PCXE_AUDIT.json')); X = json.load(open('PCXE_EXTERNALS.json')); H = json.load(open('PCXE_HAND_MODELS.json'))
ST = json.load(open('PCXE_ALL_STATUS.json'))['modules']; sbm = json.load(open('PCXE_SPLITB_HITS.json'))['modules']
S = '/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partE'
cm = json.load(open(S + '/compose2_modules.json'))
sb = N['sb']
# ---------------- trust naming
dep = []; byrow = collections.Counter(); conds = []
for m, dd in ST.items():
    for n, r in dd.items():
        if r['status'] == 'DEPENDS_ON_LIBRARY_TRUST':
            assert r.get('trust_rows'), (m, n)
            c = cm.get(m, {}).get('definitions', {}).get(n)
            dep.append(dict(module=m, definition=n, trust_rows=r['trust_rows'], theorem=r.get('theorem'), previous_status=r.get('previous_status'), in_splitB_cone=bool(c and c['in_splitB_cone']), in_CLOSED_root_cone=bool(c and c['in_CLOSED_root_cone']), phase=r.get('decided_by'),
                            aspis_side_residue_not_separated=r.get('aspis_side_residue_not_separated'), condition=r.get('condition')))
            for t in r['trust_rows']: byrow[t.split(' (')[0]] += 1
        if r['status'] == 'CONDITIONAL_ON_BINDING' and r.get('trust_rows'):
            conds.append(dict(module=m, definition=n, trust_rows_also_named=r['trust_rows']))
rows_def = {'HM-A': 'SDK type models (Pubkey, Hash, PubkeyError, ProgramError; solana_sdk_ids bpf_loader_upgradeable.id is not named in the HM-A text today)', 'HM-B': 'core slice and array iterator models (chunks_exact_mut, ChunksExactMut::next, IterMut/IntoIter into_iter)',
            'HM-C': 'Option/Result combinators (ok_or, map, map_err, Try::branch, from_residual, Option eq, TryReserveError)', 'HM-D': 'array and slice operations excluding from_fn (Array::map, slice/array eq, windows, first, RangeFull index ops)',
            'HM-F': 'num/ops/iter models (count_ones, trailing_zeros, Range clone, revFold, rangeFold, Iterator all/any)', 'HM-G': 'Aeneas discriminant helpers (read_discriminant, ImportUnionNamedDiscriminant registration, transport.Variant)',
            'CrossCrateConstantEncoding': 'link between an Aeneas external axiom of type Result X for a cross-crate constant and a transparent value', 'ReviewedTranscription-PublicPreparation.public_bytes': 'ADDED-LEAD-20261110 row; evidence/public-bytes-20261110, NPL_PublicBytes.gate_eq, gate_total_length; removal: an Aeneas emission proved equal'}
json.dump(dict(schema='PCXE_TRUST_NAMING/1', target_established=False,
  rule='A DEPENDS_ON_LIBRARY_TRUST record is a definition for which a Lean equality or a binding statement exists and the only outstanding item is a named trust row (library model, constant-encoding link, or the reviewed transcription row). It is counted in its own class, never as proved. No row was added to any document; the row names are those of PCVG_TRUST_ROWS.md (proposals) and the lead-added ReviewedTranscription row.',
  rows=rows_def, records=dep, counts=dict(records_table=len(dep), records_in_deployed_splitB=sum(1 for d in dep if d['in_splitB_cone']), by_row_name_mentions=dict(byrow)), conditional_records_that_also_name_a_row=conds,
  rows_with_zero_records=['HM-C (no record is DEPENDS_ON_LIBRARY_TRUST on HM-C alone: only the PublicPreparation 26 are, together with the ReviewedTranscription row, and those definitions sit outside the deployed_splitB cone constants)', 'HM-D', 'HM-F', 'HM-G'],
  pp_note='AspisR1PublicPreparation.Funs: 26 definitions proved fresh = gate (P3l, PCVL_L007). Six depend on the callee core.result.Result.map_err (HM-C) resolving to the gate by name, and three of those six also on Public.public_bytes (ReviewedTranscription-PublicPreparation.public_bytes); all six are DEPENDS_ON_LIBRARY_TRUST naming those rows; the other 20 are EQUALITY_PROVED. The headline cone reaches only one constant of this module (aspis_core.field.P), so none of the six is counted in the deployed_splitB definition totals.'),
  open('PCXE_TRUST_NAMING.json', 'w'), indent=1)
# ---------------- L187 addendum
L = json.load(open('PCXE_L187_RECONCILE.json'))
ctl = json.load(open('../prov-p1j-20261110/PCVJ_selfcopy_control.json'))
L['pcxe_addendum_AspisR1PublicPreparation_Funs'] = dict(flag='L187 flag on AspisR1PublicPreparation/Funs.lean (compiled copy sha256 544b75b9, PCVJ L003)', settled=True,
   result='The committed s1-prepared-claim-carrier-bridge copy (sha256 544b75b962ad..., 2872 lines) is definitionally equal to every compiled constant it declares: 87 of 87 equalities (PCVJ_L003, PRVEq_PPselfcopy_s3.lean, exit 0, 25.5 s, 3.08 GB). The other committed copies (4c9e3bad, f4aee266, 47d1a77f, 7d473da9, e98bb123) were not tested and are not the compiled copy.',
   caveat='71 of the 87 print only propext/Classical.choice/Quot.sound; 16 (the Debug fmt functions and instances) depend on native-decide axioms inside the gate text itself and are not credited here.',
   downstream='P3l (PCVL_L007) proves fresh 4bb3b3f-extraction text equal to this compiled gate for 26 definitions; six depend on public_bytes (ReviewedTranscription) and map_err (HM-C). The headline cone reaches one constant of this module.',
   control=ctl['scope'])
json.dump(L, open('PCXE_L187_RECONCILE.json', 'w'), indent=1)
# ---------------- non-frozen owner status
NF = json.load(open('PCXE_NONFROZEN.json'))
for m, v in NF['modules'].items():
    v['owner_status_2026_11_10'] = ('OPEN_UNTIL_FRESH_4bb3b3f_EQUALITY_FOR_EVERY_DEFINITION: condition met at definition level (every definition equal to a fresh 4bb3b3f emission)' if v['verdict'] == 'ALL_DEFINITIONS_EQUALITY_PROVED'
                                    else 'OPEN: owner decision 2026-11-10, never kept as-is; replaced by a fresh 4bb3b3f extraction with equality for every definition (not yet: ' + v['verdict'] + ')')
NF['owner_status_note'] = ('Owner decision 2026-11-10 (via lead): one Rust model (crates/ incl. aspis-prover, programs/r1-cost-probe, Cargo.lock at 4bb3b3f; programs/aspis-pool at b936275). The 26 non-frozen gate modules in the soundness cone are to be replaced by fresh 4bb3b3f extraction with equality, never kept as-is. '
                           'Counted here: 4 modules meet the condition at definition level (still ' + 'subject to the detector-blind and Types-isomorphism caveats recorded per module), 22 are OPEN (21 UNVERIFIED detector-blind, 1 OPEN). No module is counted as accepted as it stands.')
json.dump(NF, open('PCXE_NONFROZEN.json', 'w'), indent=1)
# ---------------- classifications
C = [
 ('PCXE-C1', 'Base: PCQI_ALL_STATUS.json (P1i merged over PCUJ, 49 NO_FRESH_EMISSION definitions EQUALITY_PROVED) plus overlays from PCVF_ (P3f), PCVH_ (P3h), PCVI_ (P3i), PCVK_ (P3k), PCVL_ (P3l) and the PCVG_ triage, written by PCXE_overlay.py (log: PCXE_OVERLAY_LOG.json). Every overlay record names its theorem, file, scope and receipt; each receipt was checked for exit 0 and standard axioms only. No record is moved down; a record is moved up only on an exit-0 scope.', 'Per the brief: status inputs merged on top of PCUJ/PCQI.'),
 ('PCXE-C2', 'Classes. EQUALITY_PROVED only where the statement has no outstanding hypothesis. CONDITIONAL_ON_BINDING where the theorem quantifies over an Ext/Bound record (Aspis packet boundaries, deployed instantiation not shown). DEPENDS_ON_LIBRARY_TRUST where the only outstanding item is a named trust row; own class, never proved. OPEN otherwise.', 'Brief: wrong-basis records are OPEN, binding results are CONDITIONAL, DEPENDS_ON_LIBRARY_TRUST is its own class.'),
 ('PCXE-C3', 'Port23PUSH push and update_residue_row (P3i, PCVI_L003): outstanding item is that the into_iter parameter f is the library into_iter: DEPENDS_ON_LIBRARY_TRUST, HM-B. update_residue_row was CONDITIONAL_ON_BINDING (P3d) and moves sideways; the P3d proving file is no longer credited (superseded by the P3i file); its P3d theorem stays in the combined import from the earlier bundle.', 'Library-only hypothesis.'),
 ('PCXE-C4', 'Port5Q2 weights is CONDITIONAL_ON_BINDING with HM-B named in addition: it depends both on the read := fresh Reader.k instantiation and on the IterMut binding; weights_loop is CONDITIONAL on the instantiation only.', 'Mixed hypotheses are not library-only.'),
 ('PCXE-C5', 'WideToBytes x4 (to_le_bytes in two modules, loop, loop.body): DEPENDS_ON_LIBRARY_TRUST, HM-B, per PCVG_REMAINING.json (lead ruling). No Lean equality exists for them; the Aspis-side loop arithmetic is not separated from the iterator part. Flag aspis_side_residue_not_separated; they carry no theorem and are not credited as proofs. This is a triage class, the weakest in DEPENDS_ON_LIBRARY_TRUST.', 'Recorded exactly as the lead classified them; no inflation.'),
 ('PCXE-C6', 'PCQI_REMAINING classed four P1i records DEPENDS_ON_LIBRARY_TRUST (derived PartialEq::eq on QM31 and WideExact; NID resume and its closure). Not carried: no HM-A..HM-G row names the derive(PartialEq) expansion on Aspis types, and verifier.resume calls Aspis externals (QM31.from_le_bytes, checkpoint_size, Variant.tag) besides Iter.any, so it is not library-only. They stay OPEN; the missing row is listed for the owner.', 'A DEPENDS_ON_LIBRARY_TRUST record needs a named row; there is none.'),
 ('PCXE-C7', 'selected_claim (RPu_FIq_Native07, P3d constant binding external := ok <gate value>): the only outstanding item is the cross-crate constant encoding link: DEPENDS_ON_LIBRARY_TRUST, CrossCrateConstantEncoding (brief names this row in the class). The six PRVD parametric transports over opaque externals stay CONDITIONAL_ON_BINDING.', 'Brief item.'),
 ('PCXE-C8', 'PublicPreparation (P3l, PCVL_L007, 26 definitions fresh = gate). The callee closure of each definition was computed from the file text (PCXE_OVERLAY_LOG.json pp_callee_closure): six reach map_err (HM-C) and three of those also public_bytes (ReviewedTranscription-PublicPreparation.public_bytes, not a library row); all six are DEPENDS_ON_LIBRARY_TRUST naming those rows; 20 reach neither and are EQUALITY_PROVED. Gate Public.public_bytes was emitted from the mirror crate aspis_r1_public_preparation, not the frozen file. The headline cone reaches one constant of AspisR1PublicPreparation.Funs, so these records do not enter the deployed_splitB totals; they are in PCXE_ALL_STATUS.json and the trust-naming table.', 'Brief: counted as dependent on ReviewedTranscription and HM-C.'),
 ('PCXE-C9', 'WideExact.from_le_bytes (R1CandidateWideParserSource) EQUALITY_PROVED (PCVH_L008), full equality on all inputs; supersedes PCQI-C6 (DIFFERENT_BODY).', 'Brief item.'),
 ('PCXE-C10', 'Top verifier results: stage1_owned, stage2_owned (P3k), prepare, tx1 (P3k), tx2_common, tx2_authenticated (P3l) are CONDITIONAL_ON_BINDING. evidence/prov-p3m-20261110 is not merged on research (research head 74a3cf93287 = this branch base), so it is not used. VTop tx1 stays OPEN (not proved by P3l).', 'Brief: use P3m only if merged when read.'),
 ('PCXE-C11', 'Port3 closures (P3f, PCVF_L015): ten with no binding are EQUALITY_PROVED, eight CONDITIONAL_ON_BINDING (from_fn, M31 eq, M31 zero). All on the OFF emission PCVF_E005; only closure_4.closure call_mut carries wrapping. Five definitions (for_range and its loops) stay HAND_ADAPTED (FibreIndex carrier and line_node/fibre_point tables).', 'Per-definition configuration rule.'),
 ('PCXE-C12', 'P3h item2: seven credited (EbyKFinish from_limbs, QueryGeometry TABLE_A/B, LOGICAL_Y1, SPLIT, Variant.folds, Stage2 Reader equiv (isomorphism)); 25 open per PCVH_CLASSIFICATIONS.json.', 'As recorded by P3h.'),
 ('PCXE-C13', 'Combined import: new bundles C18..C21 (42 new credited files; PCXD_ bundles C01..C17 reused unchanged, pinned by sha256 in the root receipt). Bundler fixes (changed shape, not a rerun): PCXE_L002 failed because a credited file leaves a namespace open at end of file; the bundler now closes unmatched namespace/section scopes (C18 byte-identical). PCXE_L004 failed on root-level helper lemma names duplicated across the three P3k files; rename rule PCXE-C5 suffixes PRVEq_<helper> with the bundle tag (C18, C19 byte-identical).', 'Tooling defects, not proof defects.'),
 ('PCXE-C14', 'Audit coverage correction: the PCXD_ root audit selected constants whose root namespace begins PRV/PCVE/PCVB, which omitted theorems declared inside a gate namespace (P3i, P3l files, older ones). PCXE_L008 adds the infix patterns .PRVEq. and .PRVFresh_: 13099 constants (4812 theorems) audited against 3710 (2782) in the first PCXE_ root run PCXE_L007 and 3340 (2472) in PCXD_. PCXE_L007 was a valid exit-0 root scope whose audit missed 3 credited names; PCXE_L008 replaces it for the audit, not by a rerun of an unchanged file.', 'Honest about a gap in the earlier audit.'),
 ('PCXE-C15', 'Non-frozen 26: all stay OPEN by owner decision unless a fresh 4bb3b3f emission equality holds for every definition; 4 meet the condition at definition level, 22 do not (PCXE_NONFROZEN.json owner_status_2026_11_10).', 'Brief.'),
 ('PCXE-C16', 'Externals: 99 unresolved split by PCVG_EXTERNALS_BY_CRATE.json into 68 aspis-frozen (41 distinct names, open obligations) and 31 library/SDK entries that name a proposed row (HM-A 16, HM-D 14, HM-F 1), counted in the DEPENDS_ON_LIBRARY_TRUST family as named-not-proved. solana_sdk_ids bpf_loader_upgradeable.id is not named in the HM-A text today.', 'Brief.'),
 ('PCXE-C17', 'L187: the AspisR1PublicPreparation/Funs flag is settled by PCVJ_L003 (committed copy 544b75b9 equals all 87 compiled constants). The 14 unrecovered and 42 versioned/renamed emission modules and the eight SOURCE_PATH_DIFFERS modules reconcile as in PCXD_ (PCXE_L187_RECONCILE.json).', 'Carried; one flag closed.'),
 ('PCXE-C18', 'Receipts record source_tree_dirty true: the evidence directory of this job was untracked when the scopes ran; uploaded sources are hashed in each receipt and equal the committed bundle files.', 'As PCXD-C11.'),
]
json.dump(dict(schema='PCXE_CLASSIFICATIONS/1', items=[dict(id=a, classification=b, reason=c) for a, b, c in C]), open('PCXE_CLASSIFICATIONS.json', 'w'), indent=1)
# ---------------- tools
def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()
ch = {'PCXE_overlay.py': 'new: PCXE_ALL_STATUS from PCQI + P3f/h/i/k/l overlays', 'PCXE_externals.sh': 'new: splits section c by crate (PCVG_)', 'PCXE_rerun.sh': 'new: local steps in order', 'PCXE_finalize.sh': 'rewritten for PCXE_',
      'PCXE_run.py': 'from PCXD_run.py; host workspace codex-pc-prov-p6t-20261110; LEAN_PATH = own PCXE_exports, p6r PCXD_exports (C14..C17), p6x PCXC_exports (C13), p6c PCXB_exports (C01..C12, WrapAdd), then the ledger30 chain',
      'PCXE_make_bundles.sh': 'from PCXD: bundle numbering from C18, closes unmatched namespace/section, root audit predicate adds .PRVEq. and .PRVFresh_', 'PCXE_rename.py': 'from PCXD: PCXE-C5 root-level PRVEq_<helper> suffix',
      'PCXE_credited.sh': 'from PCXD: status file PCXE_ALL_STATUS, phases P1i/P3f/h/i/k/l, DEPENDS_ON_LIBRARY_TRUST with a theorem is credited', 'PCXE_compose2.sh': 'from PCXD: PCXE_ALL_STATUS, DEPENDS_ON_LIBRARY_TRUST branch and rollup, trust_rows passthrough',
      'PCXE_audit.sh': 'from PCXD: status file and DEPENDS class', 'PCXE_hm3.sh': 'from PCXD: P1i/P3f-P3l hand-model files added'}
tools = [dict(file=f, sha256=sha(f), note=ch.get(f, 'from PCXD_ with paths and prefix only')) for f in sorted(glob.glob('PCXE_*.sh') + glob.glob('PCXE_*.py') + ['run_scope.sh'])]
json.dump(dict(schema='PCXE_TOOLS/1', rerun_order='PCXE_run host scopes first (run_scope.sh PCXE_L00n TARGET; PCXE_chain1.sh), then bash PCXE_rerun.sh (overlay, credited, make_bundles, reach, compose1-3, nonfrozen_final, l187, nosource, shramt, hm3, externals, trust, audit, final, delta, notattempted, rowtables), then PCXE_finalize.sh',
     scratch_inputs='compose steps read the PCO partition tables (emods_decl, emod_hits, roots, lean_index, strictpins_hashes, closed_rows) from a scratch directory cloned from the PCXA/PCXB run (partE here); the row-relevant parts are inside PCXE_ROW_TABLES.json', tools=tools), open('PCXE_TOOLS.json', 'w'), indent=1)
# ---------------- status line
ex = X['counts_pcxe']
line = (f"# PCXE status line for the next ledger\n\nTarget not yet established. The ledger job consumes PCXE_PROVENANCE.json and PCXE_ROW_TABLES.json; no ledger row was edited.\n\n"
 f"Provenance status (P6 refresh 2, PCXE_; ledger30 base 6ce07a6a593; frozen 4bb3b3f; Target not yet established). HEADLINE CONE AspisR1.TAS_FinalB.deployed_splitB (146370 constants): {sb['modules']} emitted gate modules reached, module rollups {sb['module_rollups']}; "
 f"{sb['definitions_total']} reached definitions: {sb['definitions']}; OPEN split {N['opens']} (wrong-basis counted OPEN). CLOSED-row view (599, recomputed): {N['rows']}; {N['rows_relying_on_OPEN_module']} rows rely on a module whose rollup is OPEN. "
 f"CONDITIONAL_ON_BINDING and DEPENDS_ON_LIBRARY_TRUST are their own classes and are not counted as proved. Combined import PRVCmb_ROOT (21 bundles + PRVH_WrapAdd, {json.load(open('PCXE_CREDITED_FILES.json'))['n_files']} credited files): {A['audited_theorems_per_item']} theorems audited one by one among {A['audited_constants']} constants, standard axioms only (union {A['union_axioms']}). "
 f"Hand models: {H['counts']['hand_written_gate_models']} hand-written gate models; externals without gate definition {X['n']}: {ex['a_resolved_by_gate_hand_model_or_constant']} resolved elsewhere, {ex['c_aspis_frozen_open_obligation']} aspis-frozen open obligations ({ex['c_aspis_frozen_distinct_names']} distinct names), {ex['c_library_or_sdk_row_named']} library/SDK entries naming a proposed row. "
 f"Not covered: release replay, L187/L188 (source reconciliation only), source-to-ELF; R22 owns checked-versus-wrapping.\n")
open('PCXE_STATUS_LINE.md', 'w').write(line)
# ---------------- trust proposals delta (once)
t = open('PCXE_TRUST_PROPOSALS.md').read()
if 'Delta against PCXD_TRUST_PROPOSALS.md' not in t:
    t += ("\n\n## Delta against PCXD_TRUST_PROPOSALS.md\n\nNo hand model was added by P1i, P3f-P3l (their HAND_MODELS files add none; PCVK_ lists proof-internal lemmas and a tactic). The class texts above are unchanged. Rows are now named on records (PCXE_TRUST_NAMING.json): HM-B on 6 definitions (4 WideToBytes, 2 Port23PUSH), "
          "CrossCrateConstantEncoding on 1, HM-C on 6 PublicPreparation definitions and ReviewedTranscription-PublicPreparation.public_bytes on 3 of them (outside the headline cone constants). HM-A is named on CONDITIONAL records of AdapterRw, NMT and the caller models as a further dependency. "
          "Open wording items: HM-A text does not name solana_sdk_ids bpf_loader_upgradeable.id; no row names derive(PartialEq) on Aspis types (two P1i records stay OPEN for that); HM-G may be an Aspis-side proof item (PCVG_ note); the Rust sysroot string of the pins (nightly-2026-06-01 vs 2026-09-17, client 1.94.1) must be confirmed before a row is entered. Rows are proposals; none entered.\n")
    open('PCXE_TRUST_PROPOSALS.md', 'w').write(t)
print('ok', len(dep), 'depends records;', dict(byrow))
PY
