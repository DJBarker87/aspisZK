#!/bin/bash
# PCXD_compose2.sh: PCXD_PROVENANCE.json, PCXD_R22_SPLIT.json and PCXD_STATUS_LINE inputs.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6r/evidence/prov-p6r-20261110
python3 -I -B - <<'PY'
import sys, json, re, collections, lzma
sys.path.insert(0, '.')
import PCXD_lib as L
pco = L.J('prov-p0-20261109/PCO_PARTITION.json')['modules']
c1 = json.load(open(L.SCR + '/compose1.json')); closed_rows = json.load(open(L.SCR + '/closed_rows.json'))
st = L.J('prov-p2j-20261110/PCUJ_ALL_STATUS.json')
pcuf = st['modules']
led = L.JX('ledger30-20261111/NNN_LEDGER.json.xz')
closed = sorted(r['row'] for r in led['rows'] if r['status'] == 'CLOSED')
def pmod(label):
    if label in c1: return label
    for suf in ('_Funs', '_Types'):
        if label.endswith(suf) and label[:-len(suf)] + '.' + suf[1:] in c1: return label[:-len(suf)] + '.' + suf[1:]
    return None
# ---- evidence for receipts (R group)
nkt = {e['emitted_file_sha256']: e for e in L.J('emission-audit-20261109/NKT_EXTRACTIONS.json')}
nml = {b['blob']: b for b in L.J('emission-repro2-20261110/NML_PROVENANCE.json')['blobs']}
sp = json.load(open(L.SCR + '/strictpins_hashes.json'))
need = {cd['sha256'] for m in c1 for cd in pco[m]['candidates']}
pinfile = collections.defaultdict(list)
for p, v in sp.items():
    for h in v['hashes']:
        if h in need: pinfile[h].append(p)
del sp
def receipts(cd):
    s = cd['sha256']; out = []
    e = nkt.get(s)
    if e and e.get('pin_receipts'): out += [str(x) for x in e['pin_receipts'][:3]]
    b = nml.get(s)
    if b and b['verdict'].startswith('REPRODUCED'): out.append('emission-repro2-20261110/NML_PROVENANCE.json blob ' + s[:12] + ' run ' + str(b.get('run')))
    out += pinfile.get(s, [])[:3]
    return out or ['(status derived by PCO_partition.py from strict-receipt hash membership; path not recoverable in this snapshot)']
# ---- per module / definition
OPENR = lambda **k: dict(status='OPEN', **k)
out_mod = {}
for m, d in c1.items():
    g = pco[m]; ann = set(d['annotated']); pm_recs = {}
    for label, defs in pcuf.items():
        if pmod(label) == m: pm_recs.update(defs)
    names = set(d['splitB_names']) | set(d['closed_names'])
    defs_in_scope = sorted(((names & ann) | (names & set(pm_recs))))
    recs = {}
    for n in defs_in_scope:
        cls = d['arith'].get(n)
        r = pm_recs.get(n)
        base = dict(in_splitB_cone=n in d['splitB_names'], in_CLOSED_root_cone=n in d['closed_names'], arithmetic_class=cls)
        if r:
            s = r['status']
            common = dict(base, configuration=r.get('configuration'), required_configuration=r.get('required_configuration'), aeneas_tool=r.get('aeneas_tool'), theorem=r.get('theorem'), proving_file=r.get('proving_file'), receipt=r.get('receipt'), decided_by=r.get('decided_by'), pcqh_status=s)
            if s == 'OPEN':
                rs = r.get('open_reason') or ''
                recs[n] = dict(common, status='OPEN', open_reason=rs, open_class=('WRONG_BASIS' if rs.startswith('WRONG_BASIS') else 'NO_FRESH_EMISSION' if rs.startswith('NO_FRESH_EMISSION') or 'NO_FRESH_EMISSION' in rs[:40] else 'NO_RECORD' if rs.startswith('no Lean equality') else 'FAILED_OR_OTHER'))
            elif s in ('HAND_ADAPTED', 'NO_FROZEN_COUNTERPART'): recs[n] = dict(common, status=s, open_reason=r.get('open_reason'))
            elif s == 'CONDITIONAL_ON_BINDING': recs[n] = dict(common, status='CONDITIONAL_ON_BINDING', condition=r.get('open_reason'), note=r.get('notes'))
            elif s == 'EQUALITY_DOMAIN': recs[n] = dict(common, status='EQUALITY_DOMAIN', semantic_class='loop-return refinement (fresh Option-Bool loop return refines gate Bool loop), not a plain equality')
            elif s == 'RECEIPTED': recs[n] = dict(common, status='RECEIPTED', configuration='per receipt (not re-derived)')
            else: recs[n] = dict(common, status=s, binding_upgrade=r.get('binding_upgrade'), config_bridge=bool(r.get('config_bridge')), encoding_bridges=r.get('encoding_bridges'))
        elif g['group'] == 'R':
            recs[n] = dict(base, status='RECEIPTED', configuration='per receipt (not re-derived)', aeneas_tool='per receipt (not re-derived)', evidence=[x for cd in g['candidates'] for x in receipts(cd)][:3])
        else:
            sub = g['subgroup']
            recs[n] = dict(base, status='OPEN', open_class='NO_RECORD', open_reason=f'no Lean equality record for this definition (module group {g["group"]}: {sub})', configuration='NA', aeneas_tool='NA')
        # PCXD overlays (corrections 1, 2, 6 of the PCXD brief)
        P3B = {('AspisV8R19.ComplexFieldSlice', 'AspisR65Field.field.M31.mul'): ('PRVEq.AspisV8R19.ComplexFieldSlice.field.M31.mul', 'prov-p3b-20261109/PRVEq_AspisV8R19_ComplexFieldSlice_P3.lean', 'PCVB_L042'),
               ('AspisV8R19.GuardedFieldSlice', 'AspisR64Field.field.M31.mul'): ('PRVEq.AspisV8R19.GuardedFieldSlice.aspis_core.field.M31.mul', 'prov-p3b-20261109/PRVEq_AspisV8R19_GuardedFieldSlice_P3.lean', 'PCVB_L043'),
               ('AspisV8R19.QuarticFieldSlice', 'AspisR66Field.field.M31.mul'): ('PRVEq.AspisV8R19.QuarticFieldSlice.field.M31.mul', 'prov-p3b-20261109/PRVEq_AspisV8R19_QuarticFieldSlice_P3.lean', 'PCVB_L041')}
        if (m, n) in P3B:
            th, pf, sc = P3B[(m, n)]
            recs[n] = dict(recs[n], status='EQUALITY_PROVED', open_reason=None, open_class=None, theorem=th, proving_file=pf, decided_by='P3b (PCVB_), credited by PCXD-C2', previous_status='OPEN (P2f FAILED: unsolved goals)',
                           basis_class='ON_EMISSION_MATCHING_P3B_FULL_EQUALITY', note=f'fresh = gate as functions M31 -> M31 -> Result M31 with no hypotheses; same fresh emission (sha256 in the file header equals the P2f record emission) and same gate constant as the P2f record; scope {sc} exit 0')
        wc = L.WRAPPING_CLOSURE
        if n in wc.get(m, ()):  # nine definitions whose gate carries wrapping on plain operators: OFF emission is the correct basis (lead ruling), recorded
            recs[n]['configuration'] = 'OFF'; recs[n]['required_configuration'] = 'OFF (gate carries wrapping_* on plain operators; per-definition ruling of 2026-11-10)'; recs[n]['basis_class'] = 'OFF_EMISSION_WRAPPING_CLOSURE'
        elif r and (r.get('pcuj_basis_note') or r.get('pcui_basis_note')) and recs[n]['status'] == 'EQUALITY_PROVED':
            recs[n]['basis_class'] = r.get('pcuj_basis_note') or r.get('pcui_basis_note')
            if recs[n]['basis_class'] == 'OFF_EMISSION_WRAPPING_DECL': recs[n]['configuration'] = 'OFF'
        if recs[n]['status'] == 'EQUALITY_PROVED' and str(recs[n].get('theorem') or '').split(' ;')[0].endswith('.equiv'):
            recs[n]['record_kind'] = 'ISOMORPHISM_OF_TYPES_DECLARATIONS (Equiv, constructor-wise or structure-wise)'
        # ShrAmt: NPE_ (evidence/shramt-20261110, NPE_SHRAMT_CHECK.md) verified the bridge in the overflow-checks-OFF configuration; records that carried the encoding bridge are marked
        if r and any('ShrAmt' in str(x) for x in (r.get('encoding_bridges') or [])) and recs[n]['status'] == 'EQUALITY_PROVED':
            recs[n]['shramt_bridge'] = 'upgraded_from_conditional_on_ShrAmt_by_NPE_2026-11-10'
        # P3e (PCVE_) overlay + NPE_ upgrade (lead addenda): transport row family
        if m == 'RPz7_FIo_NativeFuns' and n.endswith(('transport.Variant.row_loop.body', 'transport.Variant.row_loop', 'transport.Variant.row')):
            isrow = n.endswith('Variant.row')
            recs[n] = dict(recs[n], status='EQUALITY_PROVED' if isrow else 'EQUALITY_DOMAIN', domain_hypothesis=None if isrow else 'iter.end <= 16',
                           semantic_class=None if isrow else 'domain-restricted equality: the fresh OFF body and the gate body DIFFER for iter.end above the checked-shift bound; equal for iter.end <= 16',
                           theorem='PCVE.transport.' + n.split('transport.')[1] + ('_dom' if 'row_loop' in n else ''), proving_file='prov-p3e-20261109/PRVEq_transport_row_P3.lean (PCVE_L006, research 3ba71246350; copy PRVEq_transport_row_P3.lean in this directory)',
                           previous_status=s if r else 'OPEN', shramt_bridge='upgraded_from_conditional_on_ShrAmt_by_NPE_2026-11-10', configuration='OFF', required_configuration='OFF (mixed configuration inside the body: checked shifts in the gate, wrapping in the OFF emission)')
    cnt = collections.Counter(r['status'] for r in recs.values())
    if g['group'] == 'R': roll = 'RECEIPTED'
    elif not recs: roll = 'NO_ANNOTATED_DEFINITION_REACHED' if g['group'] != 'R' else 'RECEIPTED'
    elif cnt['OPEN'] or cnt['HAND_ADAPTED'] or cnt['NO_FROZEN_COUNTERPART']: roll = 'OPEN'
    elif cnt['CONDITIONAL_ON_BINDING']: roll = 'CONDITIONAL'
    elif cnt['EQUALITY_DOMAIN']: roll = 'EQUALITY_DOMAIN'
    else: roll = 'EQUALITY_PROVED'
    cfgs = collections.Counter(r.get('configuration', 'NA') for r in recs.values())
    out_mod[m] = dict(group=g['group'], subgroup=g['subgroup'], kind=g['kind'], rollup=roll, counts=dict(cnt), n_defs=len(recs), in_splitB_cone=bool(d['splitB_names']), in_CLOSED_root_cone=bool(d['closed_names']),
                      n_rows=g['n_rows'], module_configuration=dict(cfgs), compiled_source_ambiguous=g.get('compiled_source_ambiguous', False), candidates=[dict(sha256=cd['sha256'], status=cd['status']) for cd in g['candidates']],
                      hand_or_unannotated_names_reached=len(names - ann - set(pm_recs)), definitions=recs)
json.dump(out_mod, open(L.SCR + '/compose2_modules.json', 'w'))
# ---- rows
roots_rows = json.load(open(L.SCR + '/roots.json'))
rows = {}
for row in closed:
    ms = {}; openmods = collections.Counter(); anyroot = False
    for m, d in closed_rows.items():
        if row in d:
            anyroot = True; ns = set(d[row]); recs = out_mod[m]['definitions']
            reached = [n for n in ns if n in recs]
            nopen = sum(1 for n in reached if recs[n]['status'] not in ('RECEIPTED', 'EQUALITY_PROVED', 'EQUALITY_DOMAIN'))
            if nopen: openmods[m] = nopen
            ms[m] = (len(reached), nopen)
    has_root = any(row in v for v in roots_rows.values()) 
    if not anyroot: rows[row] = dict(status='NO_EMITTED_MODULE_REACHED' if has_root else 'UNASSESSED_ROOTLESS')
    else: rows[row] = dict(status='CONDITIONAL' if openmods else 'PROVENANCE_CLEAN_AT_DEFINITION_LEVEL', n_emitted_modules_reached=len(ms), n_open_definitions=sum(openmods.values()), open_modules=dict(openmods))
cr = collections.Counter(r['status'] for r in rows.values())
json.dump(rows, open(L.SCR + '/compose2_rows.json', 'w'))
tot = lambda sel: collections.Counter(r['status'] for m, v in out_mod.items() if sel(v) for r in v['definitions'].values())
print('rows', cr)
print('splitB defs', tot(lambda v: False))
sbd = collections.Counter(); sbm = collections.Counter(); clm = collections.Counter(); cld = collections.Counter()
for m, v in out_mod.items():
    for n, r in v['definitions'].items():
        if r['in_splitB_cone']: sbd[r['status']] += 1
        if r['in_CLOSED_root_cone']: cld[r['status']] += 1
    if v['in_splitB_cone']: sbm[v['rollup']] += 1
    if v['in_CLOSED_root_cone']: clm[v['rollup']] += 1
print('splitB modules', sbm, 'defs', sbd); print('closed modules', clm, 'defs', cld)
PY
