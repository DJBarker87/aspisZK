#!/bin/bash
# PCXE_hm3.sh: PCXE_HAND_MODELS.json (per-module hand-model inventory), PCXE_EXTERNALS.json (a/b/c classification), from PCXA_HAND_MODELS.json (924 deduplicated campaign entries) plus the records of the jobs after PCXA.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6t/evidence
python3 -I -B - <<'PY'
import json, collections, re, sys
sys.path.insert(0, 'prov-p6t-20261110')
import PCXE_lib as L
H = json.load(open('prov-p6s-20261109/PCXA_HAND_MODELS.json'))['entries']
sb = L.J('prov-p6t-20261110/PCXE_SPLITB_HITS.json')['modules']
mods = json.load(open(L.SCR + '/compose2_modules.json'))
hw = [x for x in H if x['category'].startswith('HAND_WRITTEN')]
hw_names = collections.defaultdict(set)
for x in hw: hw_names[x['name']].add(x['gate_module'])
unres = [x for x in H if x['category'] == 'NO_GATE_DEFINITION_FOUND_IN_EXAMINED_FILES']
ROW = {'option_ok_or': 'AspisR1.Port1_Library.TrustedStd.option_ok_or (ACCEPTED-ELSEWHERE; LOG D157, C3-BIN 2026-10-23 18:05)', 'allocator': 'AspisR1.S2W_D189Wrappers.Allocator.allocate / .cleanup (NAMED-IN-CONTRACT, Allocator section 3; data-only interface)'}
a = []; b = []; c = []
for x in unres:
    n = x['name']; m = x['gate_module']
    cone = x['splitB_cone_constants_matching']; cl = x['CLOSED_root_constants_matching']
    rec = dict(gate_module=m, name=n, class_=x['class_'], sources=x['sources'], reached_by_splitB_module=x['reached_by_splitB_module'], reached_by_splitB_cone_constant=x['reached_by_splitB_cone_constant'])
    if cone or cl:
        rec.update(resolved_by='gate constant of the same name present in the deployed_splitB cone list' if cone else 'gate constant of the same name present in a CLOSED-root reach list', example=(cone or cl)[0]); a.append(rec)
    elif len(hw_names.get(n, set()) - {m}) > 0:
        rec.update(resolved_by='hand-written gate model of the same name in another module: ' + ', '.join(sorted(hw_names[n] - {m})[:4])); a.append(rec)
    elif re.search(r'option\.Option\.ok_or|Option\.ok_or$', n):
        rec.update(trust_row=ROW['option_ok_or']); b.append(rec)
    elif re.search(r'(^|\.)(allocate|cleanup)$', n) and x['class_'].startswith('e_'):
        rec.update(trust_row=ROW['allocator']); b.append(rec)
    else: c.append(rec)
cc = collections.Counter(x['class_'] for x in c)
ext = dict(schema='PCXE_EXTERNALS/1', target_established=False, n=len(unres),
  rule='(a) external name equals a constant in the deployed_splitB cone list or a CLOSED-root reach list (suffix match, over-approximate), or a hand-written gate model of the same name in another module; (b) covered by a literally matching existing row of design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md (cited); (c) neither. (c) is an UPPER bound for genuinely unresolved: the gate sources were not exhaustively searched beyond the examined files and the cone/reach lists. The SDK type models (Pubkey, Hash, ...) and the core slice-iterator model are NOT matched by any trust row: the appendix SDK rows are the account-data RefCell/borrow fields, not the type models.',
  counts=dict(a_resolved_by_gate_hand_model_or_constant=len(a), b_covered_by_existing_trust_row=len(b), c_genuinely_unresolved=len(c)), c_by_class=dict(cc), a=a, b=b, c=c)
json.dump(ext, open('prov-p6t-20261110/PCXE_EXTERNALS.json', 'w'), indent=1)
print(ext['counts'], dict(cc))
# ---- per-module inventory
per = collections.defaultdict(list)
for x in hw:
    per[x['gate_module']].append(dict(name=x['name'], class_=x['class_'], category=x['category'], pinned_crate=x['pinned_crate'], reached_by_splitB_cone_constant=x['reached_by_splitB_cone_constant'], splitB_cone_constants_matching=x['splitB_cone_constants_matching'], reached_by_CLOSED_module=x['reached_by_CLOSED_module'], n_CLOSED_rows_via_module=x['n_CLOSED_rows_via_module'], sources=x['sources']))
SHR = 'ShrAmt bridge: verified against Rust semantics and the pinned translation, NPE_ 2026-11-10 (overflow-checks-off only; never reuse for checked shifts with amounts wider than 32 bits)'
dep23 = json.load(open('prov-p3d-20261109/PCVD_HAND_MODELS.json'))['hand_models']
afc = [h for h in dep23 if h['name'].startswith('core.array.from_fn')][0]; off = [h for h in dep23 if h['name'].startswith('compact.OFF')][0]
named = [
 dict(name='ShrAmt (shift amount read as Rust `as u32`; Std.Usize.wrapping_shr/wrapping_shl fresh wrappers)', inventory_line=SHR, source='prov-p1h-20261109/PCQH_HAND_MODELS.json PCQH-C2; evidence/shramt-20261110/NPE_SHRAMT_CHECK.md and NPE_ShrAmt.lean (research)',
      status='VERIFIED_BY_NPE_ for the overflow-checks-OFF configuration; Lean proof with standard axioms for every I32 and every Usize amount, << and >>',
      residuals=['Not checked against an SBF-target build (the runtime tests were x86_64).', "Relies on Lean's usize width equalling the target's, which every gate module already shares.", 'In CHECKED mode the bridge is NOT faithful for usize amounts >= 2^32 and must never be used there.'],
      removal_condition_was='MIR check of the Aeneas/Charon translation of Rust >> (now done by NPE_)', definitions_upgraded_by_it='PCXE_SHRAMT_UPGRADED.json (35 records: NFN fast_domain/for_range family incl. fibre_point, plus the transport row family)'),
 dict(name='array_from_fn_copy (gate hand model standing in for the opaque external core.array.from_fn)', kind='hand model; the fresh original-Aeneas emission has core.array.from_fn as an unconstrained axiom, the gate carries array_from_fn_copy N CopyInst FnMutInst zero init (a defined loop)', pinned_crate='Rust core library at the pinned nightly sysroot (core::array::from_fn)',
      bridge='for each instantiation: core.array.from_fn N inst f = array_from_fn_copy N CopyT inst zero_T f; NOT assumed and NOT proved (needs per-element-type Copy and zero; PCVC)', blocked_dependants=afc['blocked_definitions'], n_dependants=len(afc['blocked_definitions'])),
 dict(name='compact.OFF_* (Ops-instance constants of CurrentCompactCallerModelV1)', blocked_definitions=off['blocked_definitions'], kind='hand-written parametric constants; equalities stand only after binding'),
 dict(name='Port3_NativeGeometryBody / Port4C_NativePrefix / Port5Q2_ReaderWeights / AdapterRwModel parametric records', kind='gate functions are parametric in a hand-written record (Ops, Leaves, ReadK+IterMut model, AdapterRw.Ops); fresh calls the externals as axioms; carriers differ', status='HAND_ADAPTED (23 + 3 + 2 + 9 definitions, PCUH_HAND_MODELS.json); no equality; counted HAND_ADAPTED, not EQUALITY_PROVED'),
 dict(name='cross-crate constant encoding assumption', one_line='A fresh external axiom of type Result X for a cross-crate constant is linked to a transparent value (ok <gate value>, or by name to the gate constant); the link between the Aeneas external axiom and the transparent value is itself an encoding assumption, proved only for M31.ZERO/ONE and QM31.ZERO/ONE (PRVEq_const_bind, PCUH_L035/L037) and open for the rest (state_only_hiding STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS, Native07 selected_claim, Native13 COPY_PATTERNS literal, parametric transports).', source='PCUH item 4; PCVD cross-crate constant shims'),
]
out = dict(schema='PCXE_HAND_MODELS/1', target_established=False,
  note='Per-module inventory of hand-written gate models (campaign union, 924 deduplicated entries from PCXA plus the post-PCXA jobs P1g/P1h/P2g/P2h/P3b-d/P4e). Record only: no trust row exists or is added. Named items first. The hand-written flag is a classification, not an audit of model bodies.',
  counts=dict(entries_union=len(H), hand_written_gate_models=len(hw), hand_written_reached_by_splitB_cone_constant=sum(1 for x in hw if x['reached_by_splitB_cone_constant']), unresolved_externals=len(unres), a=len(a), b=len(b), c=len(c)),
  named_items=named, per_module={m: v for m, v in sorted(per.items())},
  post_pcxa_records={j: json.load(open(f)) for j, f in [('PCQH', 'prov-p1h-20261109/PCQH_HAND_MODELS.json'), ('PCUH', 'prov-p2h-20261109/PCUH_HAND_MODELS.json'), ('PCVC', 'prov-p3c-20261109/PCVC_HAND_MODELS.json'), ('PCVD', 'prov-p3d-20261109/PCVD_HAND_MODELS.json'), ('PCWE', 'prov-p4e-20261109/PCWE_HAND_MODELS.json'), ('PCQD', 'prov-p1g-20261109/PCQD_HAND_MODELS.json'), ('PCUG', 'prov-p2g-20261109/PCUG_HAND_MODELS.json'), ('PCUI', 'prov-p2i-20261110/PCUI_HAND_MODELS.json'), ('PCUJ', 'prov-p2j-20261110/PCUJ_HAND_MODELS.json'), ('PCQI', 'prov-p1i-20261110/PCQI_HAND_MODELS.json'), ('PCVF', 'prov-p3f-20261110/PCVF_HAND_MODELS.json'), ('PCVG', 'prov-p3g-20261110/PCVG_HAND_MODELS.json'), ('PCVH', 'prov-p3h-20261110/PCVH_HAND_MODELS.json'), ('PCVI', 'prov-p3i-20261110/PCVI_HAND_MODELS.json'), ('PCVJ', 'prov-p1j-20261110/PCVJ_HAND_MODELS.json'), ('PCVK', 'prov-p3k-20261110/PCVK_HAND_MODELS.json'), ('PCVL', 'prov-p3l-20261110/PCVL_HAND_MODELS.json')]})
json.dump(out, open('prov-p6t-20261110/PCXE_HAND_MODELS.json', 'w'), indent=1)
print(len(per), 'modules with hand-written models;', len(hw))
PY
