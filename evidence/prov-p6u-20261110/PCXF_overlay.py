"""PCXF_overlay.py: PCXF_ALL_STATUS.json = PCXE_ALL_STATUS.json + (1) deployed-top-body annotations (P3m..P3r), (2) the separate P1k fresh=gate record, (3) the SOURCE_REVISION AUDIT.
Run: cd evidence; python3 -I -B prov-p6u-20261110/PCXF_overlay.py
No record is moved up or down by this script: statuses are unchanged; it adds fields and corrects the source_revision label (PCXF-C1, PCXF-C2, PCXF-C4).
"""
import json, re, sys, os, collections, subprocess
sys.dont_write_bytecode = True
D = 'prov-p6u-20261110'
SCR = '/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/partF'
FROZEN_REV = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
base = json.load(open('prov-p6t-20261110/PCXE_ALL_STATUS.json'))
mods = base['modules']
log = []

# ------------------------------------------------------------------ (1) deployed top bodies
UNRELATED_TX2 = {
    'op3 parse_shape': 'deployed Tx2I_Install.shape = port of Op3I_Source parse_shape; Op3I_Source is a RECEIPTED emission of crate aspis_r1_stage2_adopted_parse_shape, not the frozen tree (PCXF_SOURCE_REVISION_AUDIT.json); related to no frozen item',
    'op5 batch_merkle': 'deployed Op5T_Install.stageBatch over a hand-adapted body; no frozen emission compared',
    'op6 query_loop': 'deployed Port3_QueryStage.query with hand-model ops dictionary; no frozen emission compared',
    'op9 BatchedWeights::finish': 'deployed Port3_FlushInstall.flush; frozen item (Vec, library rows) not extracted at the matching configuration',
    'op10 BatchedWeights::new': 'deployed Port3_NativePendingInstall.source; no gate row by name, no extraction',
    'op11 QueryGeometry::for_range': 'deployed Port3_GeometryStage.geometry; install adopted = adopted shape retired after two failed attempts (PCVN_L013, L014)',
    'op19 finish_relation': 'deployed Port4D_FinishInstall.finish; no emission of the frozen finish_relation compared',
    'read_checkpoint_semantic_alpha': 'deployed readSemanticAlpha; frozen item not extracted',
    'read_checkpoint_weights': 'deployed readWeights; frozen item not extracted',
    'QM31::from_le_bytes': 'deployed decode_k_spec + fromK with no length check; frozen item is a slice-indexed Option chain; a 16-byte-window theorem of the E32 form was not attempted',
    'aspis_core::r0::heap::filled': 'deployed OraclePortStdAllocation.filled; not compared (allocation model is a library item)',
}
RELATED_TX2 = {
    'op2 WideExact::from_le_bytes': 'PCVN_Op2.op2_frozen, PCVN_Tx2Deployed_n1.op2_deployed_frozen (fresh PCVH k1 form; all inputs); E32: PCVS_E32.e32_core, PCVS_Tx2Deployed.e32_deployed (hypothesis hE removed). Library rows HM-F (U32.from_le_bytes), HM-D (slice indexing)',
    'op13 verifier::mark': 'PCVN_Op13.op13_frozen (fresh text copied from PCQC_E011; fresh = gate by rfl)',
    'op17 weights::powers': 'PCVS_Op17.op17_frozen_bound with frozen WideExact mul/ZERO/ONE: PCVS_Eq.bind_mul, bind_zero, bind_one (emission PCVS_E001, overflow ON); the PCVN_Op17 version carried those three as binding hypotheses',
    'op18 verifier.resume (h18)': 'PCVQ_Tx2Deployed6.h18_deployed: fresh VTop resume = deployed reader resume, via PCVQ_Resumeq13.resume_sim (13 named leaf equalities, size bound) and the leaves PCVQ_Tx2Deployedq5.leaf_*, PCVQ_Validate2.validate_fresh; E32 removed by PCVS',
    'transport Variant::tag, Variant::final_len, verifier::checkpoint_size, CHECKPOINT_FIXED, QM31::ZERO': 'PCVS_Ckpt.tag_eq, final_len_eq, fixed_eq, checkpoint_size_eq, zeroK_eq (emission PCVS_E002 ON; PCVS_E001 for ZERO); composition PCVS_Tx2Deployed2.deployed_tx2_common_m/_authenticated_m (yMix)',
    'constants op14, op15, op16, op20-op23, ok_or, unwrap32': 'PCVM_Tx2Deployed_m1 (c_op0, c_op14..c_op16, c_op20..c_op23, c_unwrap32): equal to the fresh emitted constants by unfolding and v_* lemmas; op14/op15 literals 7783/7751 proved equal to the fresh OFF_ROUND1/OFF_FOLDED_ROOT',
}
LIB_TX2 = {
    'QM31 clone, QM31/WideExact PartialEq derives': 'ReviewedTranscription-FieldDerives (PCVQ_DeriveRef: field-wise transcription of the derives at field.rs:22/254/431, wide_exact.rs:27); counted apart from plain equalities',
    'Slice PartialEq eq/ne': 'HM-D', 'Iter::any': 'HM-B', 'Result::map_err': 'HM-C',
}
TX2 = dict(
    body='verifier.candidate.tx2_common / tx2_authenticated at the deployed VTop Ops (Dep := RPz7_DrvI_Installation.stage ... xdep)',
    theorems='PCVS_Tx2Deployed.deployed_tx2_common_s / deployed_tx2_authenticated_s (PRVEq_Tx2Deployed_s1, PCVS_L006); deployed_tx2_common_m / _authenticated_m (PRVEq_Tx2Deployed_s2, PCVS_L015). Chain: PCVM m1 -> PCVN n1 -> PCVQ q6 (h18 discharged, hypothesis E32 only) -> PCVS s1 (E32 discharged, no hypothesis on the callee fields)',
    class_='CONDITIONAL_ON_BINDING',
    remaining_hypotheses='the free parameters reserved, query, geo, base, finish (the deployed stage dictionaries); no h18, no hE. The Bound record is by construction satisfied by the deployed fields (xdep y Dep), which is organisation, not discharge, for every slot in slots_instantiated_only',
    slots_proved_related_to_frozen=RELATED_TX2, slots_instantiated_only_by_deployed_fields=UNRELATED_TX2, library_or_reviewed_transcription=LIB_TX2,
    reviewed_transcription_dependency=['ReviewedTranscription-FieldDerives (via the QM31 clone slot)'],
    universe_note='L187-closure universe (RPz7_DrvI, NNH seeds); not importable with the ledger30 chain in one module (PCXF_UNIVERSES.json)')
NOC_NOTE = ('corrected seed AspisR1.NOC_HostCtx.sdk c / NOC_HostSeed.m0 (op1 = NOC_HostSeed.filled reserved; non-vacuity PCVP_C.noc_op1_filled, noc_op1_ne_div). '
            'Every Bound callee field is instantiated from the Ops by rfl (organisation, not discharge). PCVP_UNRELATED.json: 18 slots have an installed-op = library-model theorem (LIB_/LIBC_) restated at the corrected seed; none relates a slot to the frozen 4bb3b3f emission of its callee.')
STAGE1 = dict(body='r1_pool_adapter::owned::stage1_owned', theorems='PCVP_S1.noc_model1 (PRVEq_AdapterStage1DeployedNOC_o1, PCVP_L005): fresh frozen stage1_owned at xOf(NOC_HostCtx.sdk c) = NOC_HostCtx.model1 c; PCVP_S1Compose.fresh_stage1_iff (PCVP_L011) composes it with NOC_Stage1Iff.iff345',
              class_='CONDITIONAL_ON_BINDING', note=NOC_NOTE, slots_proved_related_to_frozen={}, slots_instantiated_only_by_deployed_fields='all 17 callee fields',
              p3o='PCVO_S1 at NNH_CorrectConfiguration.sdk / NNH_HostSeed.m0: superseded by the corrected-seed statement, not credited separately')
STAGE2 = dict(body='r1_pool_adapter::owned::stage2_owned', theorems='PCVP_S2.noc_model2 (PRVEq_AdapterStage2DeployedNOC_o1, PCVP_L007): fresh frozen stage2_owned at xOf(NOC_HostCtx.sdk c) = NOC_HostCtx.model2 c with hashv := LIB_Env.hashv (envOf c); NOC_HostCtx.hashv c = DGP_HostDigest.hashvInst c.sha256 is not identified with it',
              class_='CONDITIONAL_ON_BINDING', note=NOC_NOTE, slots_proved_related_to_frozen={}, slots_instantiated_only_by_deployed_fields='all callee fields', p3o='as stage1')
PREP = dict(body='verifier::candidate::prepare', theorems='PCVP_C.noc_prepare, seed_prepare (PRVEq_CallerPrepTx1DeployedNOC_o1, PCVP_L003); PCVP_CComp.fresh_prepare_forward/_converse (PCVP_L013)',
            class_='CONDITIONAL_ON_BINDING', note=NOC_NOTE, slots_proved_related_to_frozen={}, slots_instantiated_only_by_deployed_fields='all 17 callee fields and six Ops fields',
            p3o='PCVO_C.deployed_prepare at NNH_HostSeed.m0 is near-vacuous (installed op1 diverges there, PCVP_C.old_op1_div) and is NOT credited')
TX1 = dict(body='verifier::candidate::tx1', theorems='PCVP_C.noc_tx1 (PCVP_L003); PCVP_CComp.fresh_tx1_forward/_converse (PCVP_L013)', class_='CONDITIONAL_ON_BINDING', note=NOC_NOTE, slots_proved_related_to_frozen={},
           slots_instantiated_only_by_deployed_fields='all callee fields', p3o='PCVO_C.deployed_tx1 at NNH_HostSeed.m0: near-vacuous, NOT credited')
TOPS = [('VTop_Model', 'VTop_Stages.verifier.candidate.tx2_common', TX2), ('VTop_Model', 'VTop_Stages.verifier.candidate.tx2_authenticated', TX2),
        ('AdapterRwModel', 'AdapterRw.r1_pool_adapter.owned.stage1_owned', STAGE1), ('NMT_stage1_owned.Funs', 'NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned', STAGE1),
        ('AdapterRwModel', 'AdapterRw.r1_pool_adapter.owned.stage2_owned', STAGE2),
        ('CurrentCompactCallerModelV1', 'AspisR1CurrentCaller.verifier.candidate.prepare', PREP), ('CurrentCompactCallerModelV1', 'AspisR1CurrentCaller.verifier.candidate.tx1', TX1)]
tops = []
for m, n, info in TOPS:
    r = mods[m][n]
    assert r['status'] == 'CONDITIONAL_ON_BINDING', (m, n, r['status'])
    r['deployed_instance'] = info; r['deployed_instance_phases'] = 'P3m, P3n, P3q, P3r' if info is TX2 else 'P3o (not credited), P3p'
    tops.append(dict(module=m, definition=n, status=r['status'], body=info['body'], theorems=info['theorems'], n_related=len(info['slots_proved_related_to_frozen']), related=sorted(info['slots_proved_related_to_frozen']),
                     instantiated_only=sorted(info['slots_instantiated_only_by_deployed_fields']) if isinstance(info['slots_instantiated_only_by_deployed_fields'], dict) else info['slots_instantiated_only_by_deployed_fields']))
    log.append(dict(module=m, definition=n, action='ANNOTATE_DEPLOYED_INSTANCE', status=r['status']))
json.dump(dict(schema='PCXF_DEPLOYED_SLOTS/1', target_established=False,
               statement='Per top body: which Bound slots are proved related to a frozen 4bb3b3f emission and which are only instantiated by deployed fields. Results are CONDITIONAL_ON_BINDING; none is a proof that the deployed path equals the frozen source. VTop tx1, NMP_prepare, NMT_tx1 stay OPEN.',
               bodies=tops, tx2=TX2, stage1=STAGE1, stage2=STAGE2, prepare=PREP, tx1=TX1,
               p3o_not_credited='PRVEq_CallerPrepTx1Deployed_o1 deployed_prepare / deployed_tx1 at NNH_HostSeed.m0 (near-vacuous); PRVEq_AdapterStage{1,2}Deployed_o1 at the NNH seed are superseded by the NOC corrected-seed statements and are not separately credited'),
          open(f'{D}/PCXF_DEPLOYED_SLOTS.json', 'w'), indent=1)

# ------------------------------------------------------------------ (2) P1k separate record (statuses unchanged)
th = json.loads(subprocess.check_output(['git', 'show', 'HEAD:evidence/prov-p1k-20261110/PCVR_STATUS.json']))['theorems_L002']
FG = 'PRVEq.AspisR1SelectedMaskProbe.Funs_k3.'
gate_mod = mods['AspisR1SelectedMaskProbe.Funs']; matched = []; nomatch = []
for t in th:
    k = 'AspisR1SelectedMaskProbe.' + t
    if k in gate_mod:
        gate_mod[k]['fresh_gate_equality'] = dict(theorem=FG + t, file='prov-p1k-20261110/PRVEq_AspisR1SelectedMaskProbe_Funs_k3.lean', scope='PCVR_L002 (exit 0, 69.3 s, peak RSS 2.53 GiB, swap 0); bundle C22 compiled in PCXF_L001',
                                                  fresh_emission='PCVR_E005 (crate aspis-core, features r0, overflow checks ON, Aeneas 959659a6, frozen 4bb3b3f)', axioms='propext, Classical.choice, Quot.sound',
                                                  note='fresh frozen aspis-core definition equals this gate definition; the gate module itself was emitted from probe crate aspis_r1_mask_extraction_probe. Status stays RECEIPTED here by rule: RECEIPTED never implies pin-equal; this field is the separate pin-equality evidence')
        matched.append(k)
    else: nomatch.append(t)
log.append(dict(action='FRESH_GATE_EQUALITY_SEPARATE', matched=len(matched), theorems_without_gate_record=nomatch))

# ------------------------------------------------------------------ (3) SOURCE_REVISION AUDIT
P = json.load(open('prov-p0-20261109/PCO_PARTITION.json'))['modules']
sp = json.load(open(SCR + '/strictpins_hashes.json'))
frozen_pin_files = {p: v for p, v in sp.items() if v['frozen']}
hash2pins = collections.defaultdict(set)
for p, v in sp.items():
    for h in v['hashes']: hash2pins[h].add(p)
FROZEN_CRATES = {'aspis_core', 'aspis_statement', 'aspis_r1_cost_probe', 'aspis_r1_cost_probe_program', 'aspis_pool'}  # crate names that exist in the frozen tree (crates/aspis-core, aspis-statement, aspis-r1-cost-probe; programs/r1-cost-probe, aspis-pool)
recs = []; verdicts = collections.Counter(); wrong = []; wrong_by_status = collections.Counter(); wrong_mod = collections.Counter()
LABEL = 'frozen 4bb3b3f'
for m, dd in mods.items():
    for n, r in dd.items():
        if r['source_revision'] != LABEL: continue
        pm = P.get(m, {}); crates = pm.get('crates', []); kind = pm.get('kind'); cov = (pm.get('reached_definitions', {}).get(n) or {}).get('coverage')
        cands = pm.get('candidates', [])
        pins_named = sorted({pf for c in cands for pf in hash2pins.get(c['sha256'], set()) if pf in frozen_pin_files})
        any_pin = sorted({pf for c in cands for pf in hash2pins.get(c['sha256'], set())})
        if r.get('fresh_emission') and r.get('decided_by') in ('P2h', 'P3f'):
            v = 'FRESH_FROZEN_EMISSION_LABEL_UNDERSPECIFIED'; new = 'frozen 4bb3b3f (fresh emission) vs gate module source (non-frozen where listed in PCUH_NONFROZEN_STATUS)'; bad = False
        elif kind in ('FROZEN_CRATE', 'REFERENCE') and crates and set(crates) <= FROZEN_CRATES and pins_named and cov == 'IDENTICAL':
            v = 'FROZEN_TREE_CRATE_PIN_NAMES_FROZEN_DEFINITION_IDENTICAL_TO_FRESH'; bad = False
            new = f'4bb3b3f by pin: emission of frozen-tree crate {"/".join(crates)}; hash-linked pin names 4bb3b3f; definition text IDENTICAL to a fresh frozen emission (PCO coverage)'
        elif kind in ('FROZEN_CRATE', 'REFERENCE') and crates and set(crates) <= FROZEN_CRATES and cov == 'COVERED_DIFFERS':
            v = 'FROZEN_TREE_CRATE_DEFINITION_DIFFERS_FROM_FRESH'; bad = True
            new = f'NOT pin-equal: emission of crate {"/".join(crates)} (frozen-tree crate name) but this definition DIFFERS from the fresh 4bb3b3f emission (PCO coverage COVERED_DIFFERS)'
        elif kind in ('FROZEN_CRATE', 'REFERENCE') and crates and set(crates) <= FROZEN_CRATES and pins_named:
            v = 'FROZEN_TREE_CRATE_PIN_NAMES_FROZEN_NOT_COMPARED'; bad = False
            new = f'4bb3b3f per pin only: emission of frozen-tree crate {"/".join(crates)}; hash-linked pin names 4bb3b3f; definition not compared to a fresh emission (coverage {cov or "not recorded"}); RECEIPTED here does not mean pin-equal'
        elif kind in ('FROZEN_CRATE', 'REFERENCE') and crates and set(crates) <= FROZEN_CRATES:
            v = 'FROZEN_TREE_CRATE_NAME_REVISION_UNVERIFIED'; bad = True
            new = f'revision unverified: emission of crate {"/".join(crates)} (a crate name that exists in the frozen tree); no pin naming 4bb3b3f contains this emission hash (pins naming any revision: {len(any_pin)}); coverage {cov or "not recorded"}'
        elif kind == 'REFERENCE':
            v = 'REFERENCE_COPY_NOT_FROZEN_TREE'; bad = True
            new = f'NOT frozen: emission of reference crate {"/".join(crates) or "(no crate header)"} (module kind REFERENCE, a hand reference copy); not pin-equal to 4bb3b3f'
        elif kind == 'PROBE_OR_CUT_CRATE':
            v = 'PROBE_OR_CUT_CRATE_NOT_FROZEN_TREE'; bad = True
            new = f'NOT frozen: emission of probe/cut crate {"/".join(crates)} (not in the 4bb3b3f tree); not pin-equal to 4bb3b3f'
        else:
            v = 'NO_CRATE_HEADER_TRANSFORMED_COPY'; bad = True
            new = 'NOT frozen: emission with no Aeneas crate header (transformed copy of a committed Lean file); source not derivable from the module header'
        verdicts[(v, r['status'])] += 1
        rec = dict(module=m, definition=n, status=r['status'], previous_label=LABEL, verdict=v, wrong_claim=bad, crates=crates, kind=kind, coverage=cov, pins_naming_frozen=pins_named[:3], n_pins_any=len(any_pin), corrected_label=new,
                   candidate_sha256=[c['sha256'] for c in cands][:3], candidate_paths=[(c.get('paths') or [''])[0] for c in cands][:2])
        recs.append(rec)
        if bad: wrong.append(rec); wrong_by_status[r['status']] += 1; wrong_mod[m] += 1
        r['source_revision_previous'] = LABEL; r['source_revision'] = new; r['source_crate'] = crates; r['source_kind'] = kind
        r['pin_equal'] = {'FROZEN_TREE_CRATE_PIN_NAMES_FROZEN_DEFINITION_IDENTICAL_TO_FRESH': True, 'FRESH_FROZEN_EMISSION_LABEL_UNDERSPECIFIED': 'by fresh emission (equality statement)'}.get(v, False if bad else 'not shown')
        r['source_revision_verdict'] = v
# records whose label was already a fresh-emission label are not touched; the label 'frozen 4bb3b3f (...)' of records with their own fresh emission is checked for a recorded emission id
other = collections.Counter()
for m, dd in mods.items():
    for n, r in dd.items():
        if r['source_revision'].startswith('frozen 4bb3b3f (fresh'):
            other['has_fresh_emission_id' if r.get('fresh_emission') else 'no_emission_id'] += 1
audit = dict(schema='PCXF_SOURCE_REVISION_AUDIT/1', target_established=False,
             how_the_field_was_populated='PCXA_PROVENANCE (origin_only, 535 records) and its predecessors set source_revision to the fixed string "frozen 4bb3b3f" for every record that had no status record from a proof phase (PCXE_overlay/PCXD compose copy it forward unchanged); records from proof phases carry "frozen 4bb3b3f (fresh emission) ..." because they compare a fresh 4bb3b3f extraction with the gate module. PCO status RECEIPTED means only: a candidate source hash appears in some pin file or an aeneas receipt (any revision, any crate): PCO_partition.py cand_status. Nothing derived the crate or revision.',
             derivation='crate from the gate module header (-- [crate]) per PCO_PARTITION modules[m].crates and kind (FROZEN_CRATE only if the header crate is one of aspis_core, aspis_statement, aspis_r1_cost_probe, aspis_r1_cost_probe_program, aspis_pool); pins naming 4bb3b3f from the pin files recomputed over the research tree (strictpins_hashes); per-definition coverage IDENTICAL / COVERED_DIFFERS / UNCOVERED from the PCO comparison with the fresh frozen emissions. Revisions of the receipted extractions themselves are not re-derived.',
             n_records_with_label=len(recs), n_wrong_claims=len(wrong), wrong_by_status=dict(wrong_by_status), n_wrong_modules=len(wrong_mod),
             verdict_counts={f'{a} | {b}': c for (a, b), c in sorted(verdicts.items())},
             selected_mask_probe=dict(module='AspisR1SelectedMaskProbe.Funs', crate='aspis_r1_mask_extraction_probe', previous_label=LABEL, n_records=len(gate_mod), fresh_gate_equality_records=len(matched), fresh_gate_equality='PCVR_L002 (46 theorems; 38 gate definitions have a record here)'),
             records=recs)
base['schema'] = 'PCXF_ALL_STATUS/1'
tot = collections.Counter(r['status'] for dd in mods.values() for r in dd.values())
base['totals'] = dict(tot); base['n_definitions'] = sum(tot.values())
base['rule'] = 'PCXE_ALL_STATUS (unchanged statuses) + PCXF overlays: deployed-top-body annotations (P3m..P3r), separate P1k fresh=gate record, source_revision audit; see PCXF_OVERLAY.log and PCXF_SOURCE_REVISION_AUDIT.json'
base['sources'] = list(base['sources']) + ['PCVM..PCVS_STATUS.json (P3m..P3r, annotations only)', 'PCVR_STATUS.json (P1k, separate field)', 'PCO_PARTITION.json + strictpins_hashes (source_revision audit)']
json.dump(base, open(f'{D}/PCXF_ALL_STATUS.json', 'w'))
json.dump(audit, open(f'{D}/PCXF_SOURCE_REVISION_AUDIT.json', 'w'), indent=1)
json.dump(dict(schema='PCXF_OVERLAY_LOG/1', log=log), open(f'{D}/PCXF_OVERLAY_LOG.json', 'w'), indent=1)
print(dict(tot)); print('label records', len(recs), 'wrong', len(wrong), dict(wrong_by_status)); print(dict(verdicts)); print('fresh_gate', len(matched), nomatch)
