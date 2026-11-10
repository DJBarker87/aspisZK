#!/bin/bash
# PCXB_compose3.sh: write PCXB_PROVENANCE.json and PCXB_R22_SPLIT.json from the compose2 tables.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence/prov-p6c-20261109
python3 -I -B - <<'PY'
import sys, json, collections
sys.path.insert(0, '.')
import PCXB_lib as L
mods = json.load(open(L.SCR + '/compose2_modules.json')); rows = json.load(open(L.SCR + '/compose2_rows.json'))
sbm = {m: v for m, v in mods.items() if v['in_splitB_cone']}
clo = {m: v for m, v in mods.items() if v['in_CLOSED_root_cone'] and not v['in_splitB_cone']}
def summ(sel, pred):
    mc = collections.Counter(v['rollup'] for v in sel.values()); dc = collections.Counter()
    for v in sel.values():
        for r in v['definitions'].values():
            if pred(r): dc[r['status']] += 1
    return dict(modules=len(sel), module_rollups=dict(mc), definitions=dict(dc), definitions_total=sum(dc.values()))
S = dict(splitB_cone=summ(sbm, lambda r: r['in_splitB_cone']), CLOSED_roots_union=summ({m: v for m, v in mods.items() if v['in_CLOSED_root_cone']}, lambda r: r['in_CLOSED_root_cone']))
wrong = sum(1 for v in sbm.values() for r in v['definitions'].values() if r['in_splitB_cone'] and r['status'] == 'OPEN' and r.get('open_reason', '').startswith('WRONG_BASIS'))
S['splitB_cone']['open_wrong_basis_definitions'] = wrong
S['rows'] = dict(collections.Counter(r['status'] for r in rows.values()))
def order(m): return (0 if mods[m]['in_splitB_cone'] else 1, mods[m]['rollup'] != 'OPEN', m)
out = dict(schema='PCXB_PROVENANCE/1', target_established=False,
  statement='Target not yet established. SNAPSHOT (first of two P6 runs). Provenance only: no ledger row, trust row, RSL or contract changed. OPEN includes every definition whose only record has a wrong basis (ruling a).',
  headline_root='AspisR1.TAS_FinalB.deployed_splitB', headline_cone_constants=146370,
  cone_evidence='integrate-20261111/NNH_L942/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz (sha256 0b316cbba462874e984430db4c9ddcaa2d902053315934a8b608eaea48d30090, verified), walker NNM_ProofDriver 46ee271b..., TAS_G0_AUDIT.json raw_ax2',
  inputs=dict(partition='prov-p0-20261109/PCO_PARTITION.json (ledger30 base 6ce07a6a593; module/blob ownership re-run reproduces module groups and row counts, one module differs: AspisR1WideToBytesSource.Funs, whose group comes from the PCO shadow/pilot correction)',
              definition_status='prov-p2f-20261109/PCUF_ALL_STATUS.json (P5, P2a-d, P2r, P3a, P4a, P2f); P4b/P4c from the audited theorem lists of PCXB_L009/L010; sibling P1f (PCQG_) not used',
              statuses='RECEIPTED | EQUALITY_PROVED | EQUALITY_DOMAIN | OPEN. EQUALITY_DOMAIN here = the 4 loop-return refinements only; no canonical-domain equality exists yet.'),
  summary=S, limits=['Definition set = annotated (Aeneas Source: doc) names reached by the cone or by a CLOSED root under the PCO ownership rule, plus any name with a PCUF record; unannotated hand-written/auxiliary names reached are counted per module (hand_or_unannotated_names_reached) and are not assigned a provenance status.',
    'Group R modules are RECEIPTED at module level; the receipt is a hash-linked extraction receipt (extraction provenance), its overflow configuration is not re-derived here (configuration "per receipt").',
    'Arithmetic class is a text detector (wrapping_* call / checked `<- a op b` bind); it is a heuristic, validated against the 10 PCUF OFF-required definitions (all WRAPPING/NO_ARITH/MIXED), and is informational for the R22 split.',
    'Row view is definition-level over the names each row root reaches; modules with no annotated definition reached are not counted as OPEN. Compiled-source-ambiguous modules (14 flagged by PCO) keep provisional groups.'],
  modules={m: mods[m] for m in sorted(mods, key=order)}, rows=rows)
json.dump(out, open('PCXB_PROVENANCE.json', 'w'))
# ---- R22 split (splitB cone)
cls = collections.defaultdict(list)
for m, v in sbm.items():
    for n, r in v['definitions'].items():
        if not r['in_splitB_cone']: continue
        a = r.get('arithmetic_class')
        k = {'WRAPPING': 'wrapping_configuration', 'CHECKED': 'checked_configuration', 'MIXED': 'checked_configuration_partly_wrapping', 'NO_ARITHMETIC': 'configuration_independent_no_arithmetic_in_body'}.get(a, 'unclassified_no_body_found')
        cls[k].append(dict(module=m, definition=n, provenance_status=r['status'], configuration=r.get('configuration'), required_configuration=r.get('required_configuration')))
R = dict(schema='PCXB_R22_SPLIT/1', target_established=False, owner='design/R22-OVERFLOW-20261021.md owns deployed-wrapping vs checked-model (the checked-to-wrapping direction). Provenance does not discharge R22.',
  rule='Per definition body in the gate text: WRAPPING = body calls wrapping_* (matches the wrapping deployed ELF directly once its extraction equality holds); CHECKED = body uses checked +,-,*,shifts in the Result monad (an overflow-ON gate: needs R22 checked-to-wrapping to reach the deployed ELF); MIXED = both; NO_ARITHMETIC = body has none, but its callees are classified separately.',
  counts={k: len(v) for k, v in cls.items()},
  counts_by_status={k: dict(collections.Counter(x['provenance_status'] for x in v)) for k, v in cls.items()},
  mixed_modules_note='RPz7_FIo_NativeFuns mixes checked and wrapping bodies; classified per definition. Configuration ruling applied per definition, as PCUF-C1.',
  caveat='Detector classes are heuristics over text; PCUF required_configuration (OFF for 10 definitions found by CONFIG_MISMATCH) is carried verbatim.', definitions=cls)
json.dump(R, open('PCXB_R22_SPLIT.json', 'w'))
print(json.dumps(S, indent=1)); print(R['counts'], R['counts_by_status'])
PY
