#!/bin/bash
# PCXF_finalize.sh: PCXF_TRUST_NAMING.json, L187 addendum, non-frozen owner status, PCXF_CLASSIFICATIONS.json, PCXF_TOOLS.json, PCXF_STATUS_LINE.md, delta section of PCXF_TRUST_PROPOSALS.md, notes in PCXF_ATTEMPTS.jsonl.
# Run after PCXF_rerun.sh. Idempotent for the JSON files; the TRUST_PROPOSALS delta and the ATTEMPTS notes are appended once (guarded).
cd /Users/dominic/ZK/.worktrees/pc-prov-p6u/evidence/prov-p6u-20261110
python3 -I -B - <<'PY'
import json, hashlib, glob, collections
N = json.load(open('PCXF_NUMBERS.json')); A = json.load(open('PCXF_AUDIT.json')); X = json.load(open('PCXF_EXTERNALS.json')); H = json.load(open('PCXF_HAND_MODELS.json'))
ST = json.load(open('PCXF_ALL_STATUS.json'))['modules']; sbm = json.load(open('PCXF_SPLITB_HITS.json'))['modules']
S = '/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partF'
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
json.dump(dict(schema='PCXF_TRUST_NAMING/1', target_established=False,
  rule='A DEPENDS_ON_LIBRARY_TRUST record is a definition for which a Lean equality or a binding statement exists and the only outstanding item is a named trust row (library model, constant-encoding link, or the reviewed transcription row). It is counted in its own class, never as proved. No row was added to any document; the row names are those of PCVG_TRUST_ROWS.md (proposals) and the lead-added ReviewedTranscription row.',
  rows=rows_def, records=dep, counts=dict(records_table=len(dep), records_in_deployed_splitB=sum(1 for d in dep if d['in_splitB_cone']), by_row_name_mentions=dict(byrow)), conditional_records_that_also_name_a_row=conds,
  rows_with_zero_records=['HM-C (no record is DEPENDS_ON_LIBRARY_TRUST on HM-C alone: only the PublicPreparation 26 are, together with the ReviewedTranscription row, and those definitions sit outside the deployed_splitB cone constants)', 'HM-D', 'HM-F', 'HM-G'],
  pp_note='AspisR1PublicPreparation.Funs: 26 definitions proved fresh = gate (P3l, PCVL_L007). Six depend on the callee core.result.Result.map_err (HM-C) resolving to the gate by name, and three of those six also on Public.public_bytes (ReviewedTranscription-PublicPreparation.public_bytes); all six are DEPENDS_ON_LIBRARY_TRUST naming those rows; the other 20 are EQUALITY_PROVED. The headline cone reaches only one constant of this module (aspis_core.field.P), so none of the six is counted in the deployed_splitB definition totals.'),
  open('PCXF_TRUST_NAMING.json', 'w'), indent=1)
# ---------------- L187 addendum
L = json.load(open('PCXF_L187_RECONCILE.json'))
ctl = json.load(open('../prov-p1j-20261110/PCVJ_selfcopy_control.json'))
L['pcxe_addendum_AspisR1PublicPreparation_Funs'] = dict(flag='L187 flag on AspisR1PublicPreparation/Funs.lean (compiled copy sha256 544b75b9, PCVJ L003)', settled=True,
   result='The committed s1-prepared-claim-carrier-bridge copy (sha256 544b75b962ad..., 2872 lines) is definitionally equal to every compiled constant it declares: 87 of 87 equalities (PCVJ_L003, PRVEq_PPselfcopy_s3.lean, exit 0, 25.5 s, 3.08 GB). The other committed copies (4c9e3bad, f4aee266, 47d1a77f, 7d473da9, e98bb123) were not tested and are not the compiled copy.',
   caveat='71 of the 87 print only propext/Classical.choice/Quot.sound; 16 (the Debug fmt functions and instances) depend on native-decide axioms inside the gate text itself and are not credited here.',
   downstream='P3l (PCVL_L007) proves fresh 4bb3b3f-extraction text equal to this compiled gate for 26 definitions; six depend on public_bytes (ReviewedTranscription) and map_err (HM-C). The headline cone reaches one constant of this module.',
   control=ctl['scope'])
json.dump(L, open('PCXF_L187_RECONCILE.json', 'w'), indent=1)
# ---------------- non-frozen owner status
NF = json.load(open('PCXF_NONFROZEN.json'))
for m, v in NF['modules'].items():
    v['owner_status_2026_11_10'] = ('OPEN_UNTIL_FRESH_4bb3b3f_EQUALITY_FOR_EVERY_DEFINITION: condition met at definition level (every definition equal to a fresh 4bb3b3f emission)' if v['verdict'] == 'ALL_DEFINITIONS_EQUALITY_PROVED'
                                    else 'OPEN: owner decision 2026-11-10, never kept as-is; replaced by a fresh 4bb3b3f extraction with equality for every definition (not yet: ' + v['verdict'] + ')')
NF['owner_status_note'] = ('Owner decision 2026-11-10 (via lead): one Rust model (crates/ incl. aspis-prover, programs/r1-cost-probe, Cargo.lock at 4bb3b3f; programs/aspis-pool at b936275). The 26 non-frozen gate modules in the soundness cone are to be replaced by fresh 4bb3b3f extraction with equality, never kept as-is. '
                           'Counted here: 4 modules meet the condition at definition level (still ' + 'subject to the detector-blind and Types-isomorphism caveats recorded per module), 22 are OPEN (21 UNVERIFIED detector-blind, 1 OPEN). No module is counted as accepted as it stands.')
json.dump(NF, open('PCXF_NONFROZEN.json', 'w'), indent=1)
# ---------------- classifications
C = [
 ('PCXF-C1', 'Base: PCXE_ALL_STATUS.json unchanged in status. No record was moved up or down in this refresh: P3m..P3r prove statements about deployed top bodies (tx2_common, tx2_authenticated, stage1_owned, stage2_owned, prepare, tx1) that are already CONDITIONAL_ON_BINDING records (VTop, AdapterRw/NMT, CurrentCompactCaller); they are added as the field deployed_instance (PCXF_DEPLOYED_SLOTS.json). VTop tx1, NMP_prepare, NMT_tx1 stay OPEN.', 'Brief item 2: CONDITIONAL_ON_BINDING, per-slot listing; Bound is instantiated by the deployed fields, organisation not discharge.'),
 ('PCXF-C2', 'P1k (PCVR_L002, 46 fresh=gate theorems for AspisR1SelectedMaskProbe.Funs, bundle C22 compiled in PCXF_L001): the 38 gate definitions that have a record stay RECEIPTED and carry the separate field fresh_gate_equality; 8 of the 46 theorems (types/constants/closure bodies) have no definition record. They are not counted as EQUALITY_PROVED here and not counted as pin-equal through RECEIPTED.', 'Brief item 1: record separately, for those definitions only.'),
 ('PCXF-C3', 'Combined import: PRVCmb_ROOT (ledger30 chain, 22 bundles, 293 credited files, one new: P1k k3) plus four by-reference audit modules for the L187-universe deployed files (PCXF_UNIVERSES.json: same module name, different object in NHT_Constants and CurrentCompactCallerModelV1; NNH_HostSeed/NOC_* exist only in L187 objs; the three PRVEq base modules clash). Not one module; reason recorded, proof status unaffected. PCXF_L003 failed in the client pre-check (import Lean not resolvable from the 9-entry L1 chain); nothing was submitted to a scope; the audit files now import only Aeneas, and the shape ran as PCXF_L004.', 'Mixed universes cannot be imported silently; changed shape, not an unchanged rerun.'),
 ('PCXF-C4', 'source_revision audit: 535 records carried the fixed string frozen 4bb3b3f (origin PCXA_PROVENANCE or P2h/P3f). It was a default, not a derivation. Each is re-derived from the module header crate, the PCO coverage and the pins that name 4bb3b3f (PCXF_SOURCE_REVISION_AUDIT.json). RECEIPTED means a hash appears in some pin or Aeneas receipt of any revision; it never implied pin-equal. Statuses are not changed by the correction.', 'Brief item 1.'),
 ('PCXF-C5', 'ReviewedTranscription: PublicPreparation.public_bytes (3 PublicPreparation DEPENDS records) and FieldDerives (QM31 clone/PartialEq, WideExact PartialEq: PCVQ_DeriveRef, used by the tx2 clone slot) are counted apart from plain equalities; the tx2 deployed bodies list FieldDerives as a dependency.', 'Brief item 3.'),
 ('PCXF-C6', 'P3o deployed_prepare / deployed_tx1 at NNH_HostSeed.m0: near-vacuous (installed op1 diverges there), not credited. P3o stage1/stage2 at the NNH seeds are superseded by the P3p statements at NOC_HostCtx.sdk / NOC_HostSeed.m0 (the headline S_host seed) and are not audited separately.', 'Brief item 2.'),
 ('PCXF-C7', 'Not re-derived: the overflow configuration of RECEIPTED emissions and the revision of the receipted extractions themselves (the audit separates crate and pin evidence only).', 'Honest limit of the source_revision audit.'),
]
json.dump(dict(schema='PCXF_CLASSIFICATIONS/1', items=[dict(id=a, classification=b, reason=c) for a, b, c in C]), open('PCXF_CLASSIFICATIONS.json', 'w'), indent=1)
# ---------------- tools
def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()
ch = {'PCXF_overlay.py': 'new: PCXF_ALL_STATUS from PCQI + P3f/h/i/k/l overlays', 'PCXF_externals.sh': 'new: splits section c by crate (PCVG_)', 'PCXF_rerun.sh': 'new: local steps in order', 'PCXF_finalize.sh': 'rewritten for PCXF_',
      'PCXF_run.py': 'from PCXE_run.py; host workspace codex-pc-prov-p6u-20261110; LEAN_PATH = own PCXF_exports, p6r PCXE_exports (C14..C17), p6x PCXC_exports (C13), p6c PCXB_exports (C01..C12, WrapAdd), then the ledger30 chain',
      'PCXF_make_bundles.sh': 'from PCXD: bundle numbering from C18, closes unmatched namespace/section, root audit predicate adds .PRVEq. and .PRVFresh_', 'PCXF_rename.py': 'from PCXD: PCXE-C5 root-level PRVEq_<helper> suffix',
      'PCXF_credited.sh': 'from PCXD: status file PCXF_ALL_STATUS, phases P1i/P3f/h/i/k/l, DEPENDS_ON_LIBRARY_TRUST with a theorem is credited', 'PCXF_compose2.sh': 'from PCXD: PCXF_ALL_STATUS, DEPENDS_ON_LIBRARY_TRUST branch and rollup, trust_rows passthrough',
      'PCXF_audit.sh': 'from PCXD: status file and DEPENDS class', 'PCXF_hm3.sh': 'from PCXD: P1i/P3f-P3l hand-model files added'}
tools = [dict(file=f, sha256=sha(f), note=ch.get(f, 'from PCXE_ with paths and prefix only')) for f in sorted(glob.glob('PCXF_*.sh') + glob.glob('PCXF_*.py') + ['run_scope.sh'])]
json.dump(dict(schema='PCXF_TOOLS/1', rerun_order='PCXF_run host scopes first (run_scope.sh PCXF_L00n TARGET; PCXF_chain1.sh), then bash PCXF_rerun.sh (overlay, credited, make_bundles, reach, compose1-3, nonfrozen_final, l187, nosource, shramt, hm3, externals, trust, audit, final, delta, notattempted, rowtables), then PCXF_finalize.sh',
     scratch_inputs='compose steps read the PCO partition tables (emods_decl, emod_hits, roots, lean_index, strictpins_hashes, closed_rows) from a scratch directory cloned from the PCXA/PCXB run (partE here); the row-relevant parts are inside PCXF_ROW_TABLES.json', tools=tools), open('PCXF_TOOLS.json', 'w'), indent=1)
# ---------------- status line
ex = X['counts_pcxe']
line = (f"# PCXF status line for the next ledger\n\nTarget not yet established. The ledger job consumes PCXF_PROVENANCE.json and PCXF_ROW_TABLES.json; no ledger row was edited.\n\n"
 f"Provenance status (P6 refresh 3, PCXF_; ledger30 base 6ce07a6a593; frozen 4bb3b3f; Target not yet established). HEADLINE CONE AspisR1.TAS_FinalB.deployed_splitB (146370 constants): {sb['modules']} emitted gate modules reached, module rollups {sb['module_rollups']}; "
 f"{sb['definitions_total']} reached definitions: {sb['definitions']}; OPEN split {N['opens']} (wrong-basis counted OPEN). CLOSED-row view (599, recomputed): {N['rows']}; {N['rows_relying_on_OPEN_module']} rows rely on a module whose rollup is OPEN. "
 f"CONDITIONAL_ON_BINDING and DEPENDS_ON_LIBRARY_TRUST are their own classes and are not counted as proved. Combined import PRVCmb_ROOT (22 bundles + PRVH_WrapAdd, {json.load(open('PCXF_CREDITED_FILES.json'))['n_files']} credited files): {A['audited_theorems_per_item']} theorems audited one by one among {A['audited_constants']} constants, standard axioms only (union {A['union_axioms']}). "
 f"Hand models: {H['counts']['hand_written_gate_models']} hand-written gate models; externals without gate definition {X['n']}: {ex['a_resolved_by_gate_hand_model_or_constant']} resolved elsewhere, {ex['c_aspis_frozen_open_obligation']} aspis-frozen open obligations ({ex['c_aspis_frozen_distinct_names']} distinct names), {ex['c_library_or_sdk_row_named']} library/SDK entries naming a proposed row. "
 f"Not covered: release replay, L187/L188 (source reconciliation only), source-to-ELF; R22 owns checked-versus-wrapping.\n")
open('PCXF_STATUS_LINE.md', 'w').write(line)
# ---------------- trust proposals delta (once)
t = open('PCXF_TRUST_PROPOSALS.md').read()
if 'Delta against PCXE_TRUST_PROPOSALS.md' not in t:
    t += ("\n\n## Delta against PCXE_TRUST_PROPOSALS.md\n\nNo hand model was added by P1i, P3f-P3l (their HAND_MODELS files add none; PCVK_ lists proof-internal lemmas and a tactic). The class texts above are unchanged. Rows are now named on records (PCXF_TRUST_NAMING.json): HM-B on 6 definitions (4 WideToBytes, 2 Port23PUSH), "
          "CrossCrateConstantEncoding on 1, HM-C on 6 PublicPreparation definitions and ReviewedTranscription-PublicPreparation.public_bytes on 3 of them (outside the headline cone constants). HM-A is named on CONDITIONAL records of AdapterRw, NMT and the caller models as a further dependency. "
          "Open wording items: HM-A text does not name solana_sdk_ids bpf_loader_upgradeable.id; no row names derive(PartialEq) on Aspis types (two P1i records stay OPEN for that); HM-G may be an Aspis-side proof item (PCVG_ note); the Rust sysroot string of the pins (nightly-2026-06-01 vs 2026-09-17, client 1.94.1) must be confirmed before a row is entered. Rows are proposals; none entered.\n")
    open('PCXF_TRUST_PROPOSALS.md', 'w').write(t)
print('ok', len(dep), 'depends records;', dict(byrow))
PY
