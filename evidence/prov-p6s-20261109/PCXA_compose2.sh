#!/bin/bash
# PCXA_compose2.sh: PCXA_PROVENANCE.json, PCXA_R22_SPLIT.json and PCXA_STATUS_LINE inputs.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6s/evidence/prov-p6s-20261109
python3 -I -B - <<'PY'
import sys, json, re, collections, lzma
sys.path.insert(0, '.')
import PCXA_lib as L
pco = L.J('prov-p0-20261109/PCO_PARTITION.json')['modules']
c1 = json.load(open(L.SCR + '/compose1.json')); closed_rows = json.load(open(L.SCR + '/closed_rows.json'))
st = L.J('prov-p2f-20261109/PCUF_ALL_STATUS.json')
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
# ---- extra module-level records: P4b / P4c audited theorems
EXTRA_CFG = {'NHV_': 'OFF', 'Multiproof': 'ON', 'AspisR1WithdrawalCaller': 'ON', 'AspisR1SemanticCallExtraction': 'ON', 'AspisR1BatchedWeightsExtraction': 'ON', 'NJT_ClaimsRef': 'OFF'}
extra = collections.defaultdict(list)   # module -> [(defrel, theorem, scope, phase, cfg)]
for a, ph in (('PCXA_L009', 'P4b'), ('PCXA_L010', 'P4c')):
    t = lzma.open(f'{a}/stdout.log.xz').read().decode()
    ax = dict((n, rest) for n, rest in re.findall(r"^'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])", t, re.M))
    for n, k in re.findall(r'^PRVEQ_KIND (\S+) (\S+)$', t, re.M):
        mm = re.match(r'PRVEq\.((?:NHV_\w+?_Funs)|(?:Multiproof\w+?\.Funs)|(?:AspisR1\w+?\.Funs)|(?:NJT_ClaimsRef_Funs))\.(.*)$', n)
        if not mm: continue
        cfg = next(v for k2, v in EXTRA_CFG.items() if mm[1].startswith(k2))
        extra[mm[1]].append((mm[2], n, a, ph, cfg))
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
        ex = [e for e in extra.get(m.replace('.', '_'), []) + extra.get(m, []) if n == m + '.' + e[0] or n.endswith('.' + e[0])]
        if g['group'] == 'R':
            recs[n] = dict(base, status='RECEIPTED', configuration='per receipt (not re-derived)', aeneas_tool='per receipt (not re-derived)', evidence=[x for cd in g['candidates'] for x in receipts(cd)][:3])
        elif r:
            s = r['status']
            if r['basis_not_correct']:
                recs[n] = dict(base, status='OPEN', open_reason='WRONG_BASIS: ' + '; '.join(r['basis_problems']) + f' (record status {s})', pcuf_status=s, configuration=r['configuration'], required_configuration=r['required_configuration'], aeneas_tool=r['aeneas_tool'], theorem=r['theorem'], receipt=r['receipt'])
            elif s in ('PROVED_RFL', 'PROVED_UNFOLD', 'PROVED_EQUIV', 'PROVED_P3'):
                recs[n] = dict(base, status='EQUALITY_PROVED', kind=s, theorem=r['theorem'], proving_file=r['proving_file'], receipt=r['receipt'], configuration=r['configuration'], required_configuration=r['required_configuration'], aeneas_tool=r['aeneas_tool'], decided_by=r['decided_by'], note=r['note'])
            elif s == 'PROVED_P3_LOOP_REFINEMENT':
                recs[n] = dict(base, status='EQUALITY_DOMAIN', semantic_class='loop-return refinement (fresh Option-Bool loop return refines gate Bool loop), not a plain equality; callee atomic_statement.encode_digest_canonical resolved by name to the gate constant', theorem=r['theorem'], proving_file=r['proving_file'], receipt=r['receipt'], configuration=r['configuration'], aeneas_tool=r['aeneas_tool'], caller_domain_theorems='none needed (no domain hypothesis; refinement statement)')
            else:
                recs[n] = dict(base, status='OPEN', open_reason=f'{s}' + (': ' + r['note'][:200] if r.get('note') else ''), pcuf_status=s, configuration=r['configuration'], required_configuration=r['required_configuration'], aeneas_tool=r['aeneas_tool'])
        elif ex:
            e = ex[0]; need_on = cls in ('CHECKED', 'MIXED')
            if need_on and e[4] == 'OFF':
                recs[n] = dict(base, status='OPEN', open_reason=f'WRONG_BASIS: {e[3]} equality {e[1]} proved against an overflow-OFF extraction but the gate body is checked-arithmetic (detector class {cls})', configuration='OFF', required_configuration='ON')
            else:
                recs[n] = dict(base, status='EQUALITY_PROVED', kind=f'{e[3]}_MODULE_LEVEL_RECORD', theorem=e[1], receipt=f'prov-p6s-20261109/{e[2]}/receipt.json (audit scope; original compile in {"PCWB_L001/L003" if e[3]=="P4b" else "PCWC_L004/L008-L010"})', configuration=e[4], required_configuration='ON' if need_on else 'ON-or-OFF (arithmetic class ' + str(cls) + ')', aeneas_tool='original Aeneas 959659a6 / aeneas-b59d5188-extended per PCWB/PCWC PINS')
        else:
            sub = g['subgroup']
            recs[n] = dict(base, status='OPEN', open_reason=f'no Lean equality record for this definition (module group {g["group"]}: {sub})', configuration='NA', aeneas_tool='NA')
    cnt = collections.Counter(r['status'] for r in recs.values())
    if g['group'] == 'R': roll = 'RECEIPTED'
    elif not recs: roll = 'NO_ANNOTATED_DEFINITION_REACHED' if g['group'] != 'R' else 'RECEIPTED'
    elif cnt['OPEN'] == 0: roll = 'EQUALITY_DOMAIN' if cnt['EQUALITY_DOMAIN'] else 'EQUALITY_PROVED'
    else: roll = 'OPEN'
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
            nopen = sum(1 for n in reached if recs[n]['status'] == 'OPEN')
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
