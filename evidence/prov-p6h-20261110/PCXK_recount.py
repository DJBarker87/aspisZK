#!/usr/bin/env python3
"""PCXK_recount.py: headline recount (the three numbers) after later merged provenance jobs.

Usage: python3 -I PCXK_recount.py [--ref research] [--job evidence-subdir:PREFIX ...] [--out PCXK_COUNTS.json] [--no-default-jobs]

Reads ONLY committed files through `git show <ref>:<path>` (stdlib only).
Baseline: evidence/prov-p6w-20261110/PCXH_PROVENANCE.json (per_definition_class) and PCXH_ROW_TABLES.json, with the
cone membership (in_splitB_cone) and the row -> module -> definitions map taken from the PCXF_ files the PCXH recount itself used.
Per job (dir:PREFIX) the exit-0 'result' events of PREFIX_ATTEMPTS.jsonl give the credited theorems: a theorem is credited iff it
appears in print_axioms of an exit-0 Lean scope with standard axioms only (propext, Classical.choice, Quot.sound) or none, and no sorryAx.
Its statement is read from the scope's source (git show); statements of the shape  `@FRESH = @GATE`  credit the gate definition
GATE (matched by gate module, from the file's imports, and name; a name found in no PCXH definition is UNMATCHED, an ambiguous one AMBIGUOUS, never guessed).
STATUS.json items whose status starts with LOOP_RETURN_REFINEMENT (theorem credited above) move the matching definition to its own class
REFINEMENT_LOOP_RETURN (listed under other). Classes: SETTLED = EQUALITY_PROVED, EQUALITY_PROVED_P1N, RECEIPTED_PIN_EQUAL, RECEIPTED_SELECTED_MASK_PROBE
(+ EQUALITY_PROVED_JOB, a definition credited by a later job); NOT SETTLED = RECEIPTED_NO_PIN_EQUAL_EVIDENCE, RECEIPTED_TEXT_DIFFERS, OPEN_NOT_REDERIVABLE, OPEN,
EQUALITY_NOT_REPLAYED_IN_L187; everything else is listed under other. A definition already in an other class (CONDITIONAL_ON_BINDING, EQUALITY_DOMAIN,
DEPENDS_ON_LIBRARY_TRUST, ...) keeps it: equality of the emission does not discharge the binding/domain condition.
"""
import json, re, subprocess, sys, collections, argparse

DEFAULT_JOBS = ['prov-p2k-20261110:PCQL', 'prov-p3u-20261110:PCVX', 'prov-p3w-20261110:PCVZ', 'prov-p3v-20261110:PCVY', 'prov-p3x-20261110:PCWF']
# Stream A lead classifications (message to this job, 2026-11-10), applied after the automatic theorem-shape credit of the named job.
# value: new class, or None = hold the definition at its baseline class (the automatic credit is withdrawn). Keys are PCXH definition keys.
LEAD = {'PCWF': {
    'AspisR72Sampler.Funs|AspisR72Sampler.field.r24_canonical_mul': 'EQUALITY_DOMAIN',                 # all limbs < P
    'NCX_Reference.Types|NCX_Reference.VerifierRegistryEntryV2': 'TYPE_ISOMORPHISM',
    'Op3I_Source|Op3I_Source.verifier.candidate.parse_shape': 'DEPENDS_ON_LIBRARY_TRUST',
    'Op3I_Source|Op3I_Source.transport.Variant.tag': None}}   # not in the lead's list of 10 SETTLED: held at OPEN_NOT_REDERIVABLE
SET = {'EQUALITY_PROVED', 'EQUALITY_PROVED_P1N', 'RECEIPTED_PIN_EQUAL', 'RECEIPTED_SELECTED_MASK_PROBE', 'EQUALITY_PROVED_JOB'}
NOTSET = {'RECEIPTED_NO_PIN_EQUAL_EVIDENCE', 'RECEIPTED_TEXT_DIFFERS', 'OPEN_NOT_REDERIVABLE', 'OPEN', 'EQUALITY_NOT_REPLAYED_IN_L187'}
UPGRADABLE = NOTSET
STD = {'propext', 'Classical.choice', 'Quot.sound'}

ap = argparse.ArgumentParser()
ap.add_argument('--ref', default='research')
ap.add_argument('--job', action='append', default=[])
ap.add_argument('--no-default-jobs', action='store_true')
ap.add_argument('--demote', default=None, help='PCXK_FAILED.json: heartbeat definitions (demote:true) and the withdrawn-row section go to OPEN, counted separately')
ap.add_argument('--out', default=None)
args = ap.parse_args()
REF = args.ref

def show(p, ref=None):
    return subprocess.run(['git', 'show', (ref or REF) + ':' + p], capture_output=True, check=True).stdout.decode()
def tryshow(p):
    r = subprocess.run(['git', 'show', REF + ':' + p], capture_output=True)
    return r.stdout.decode() if r.returncode == 0 else None
def J(p): return json.loads(show(p))

E = 'evidence/'
PCXH_P = J(E + 'prov-p6w-20261110/PCXH_PROVENANCE.json')
PCXH_R = J(E + 'prov-p6w-20261110/PCXH_ROW_TABLES.json')
PCXF_P = J(E + 'prov-p6u-20261110/PCXF_PROVENANCE.json')
PCXF_R = J(E + 'prov-p6u-20261110/PCXF_ROW_TABLES.json')
base = dict(PCXH_P['per_definition_class'])
cone = {f'{m}|{d}' for m, mm in PCXF_P['modules'].items() for d, r in mm['definitions'].items() if r.get('in_splitB_cone')}
rowdefs = {row: [f'{m}|{d}' for m, ds in mods.items() for d in ds] for row, mods in PCXF_R['row_to_module_to_definitions'].items()}
rowverdict_keys = list(PCXF_R['row_verdict'])
byname = collections.defaultdict(list)           # definition name -> [module]
for k in base:
    m, d = k.split('|', 1); byname[d].append(m)

def numbers(cls):
    c = collections.Counter(cls[k] for k in cone)
    s = sum(v for k, v in c.items() if k in SET); n = sum(v for k, v in c.items() if k in NOTSET)
    other = {k: v for k, v in c.items() if k not in SET and k not in NOTSET}
    rows = collections.Counter(); settled_only = 0
    for row, ds in rowdefs.items():
        t = collections.Counter('settled' if cls.get(k) in SET else 'not_settled' if cls.get(k) in NOTSET else 'other' if k in cls else 'unrecorded' for k in ds)
        if t['not_settled'] == 0 and t['other'] == 0 and t['unrecorded'] == 0 and t['settled'] > 0: settled_only += 1
    return dict(cone_definitions=sum(c.values()), settled=s, not_settled=n, other=sum(other.values()), other_classes=other, rows_settled_only=settled_only)

b0 = numbers(base)
assert b0['settled'] == PCXH_P['SETTLED'] and b0['not_settled'] == PCXH_P['NOT_SETTLED'], ('baseline does not reproduce PCXH', b0)
assert b0['rows_settled_only'] == PCXH_R['counts_PCXH']['ALL_REACHED_DEFINITIONS_SETTLED'], ('row baseline does not reproduce PCXH', b0)

THM = re.compile(r'^theorem\s+(\S+)\s*:\s*@(\S+)\s*=\s*@(\S+)\s*:=', re.M)
AX = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
def axioms_ok(lines):
    out = {}
    for ln in lines:
        for m in AX.finditer(ln):
            ax = {a.strip() for a in (m.group(2) or '').replace('\n', ' ').split(',') if a.strip()}
            out[m.group(1)] = ax <= STD
    return out

cls = dict(base); jobs = list(([] if args.no_default_jobs else DEFAULT_JOBS)) + args.job
report = []; unmatched = []; prev_jobs = {}
for spec in jobs:
    d, pre = spec.split(':'); jd = E + d + '/'
    att = [json.loads(l) for l in show(jd + pre + '_ATTEMPTS.jsonl').splitlines() if l.strip()]
    status = J(jd + pre + '_STATUS.json')
    changes = []; credited = {}; credited_names = set(); scopes_ok = 0; files = []
    for e in att:
        if e.get('event') != 'result' or e.get('kind') != 'lean' or e.get('exit_status') != 0: continue
        scopes_ok += 1
        pa = e.get('print_axioms') or []
        if isinstance(pa, str):
            try: pa = json.loads(pa)
            except Exception: pa = [pa]
        okthm = axioms_ok(pa); credited_names |= {n for n, v in okthm.items() if v}
        src = None
        for s in e.get('sources', []):
            if s.endswith('.lean') and e['module'] in s: src = tryshow(jd + e['attempt'] + '/sources/' + s) or tryshow(jd + s.split('/')[-1])
        if src is None: src = tryshow(jd + e['module'] + '.lean')
        if src is None: unmatched.append(dict(job=pre, module=e['module'], reason='source not found')); continue
        if re.search(r'\bsorry\b|native_decide|^axiom\s', src, re.M) and 'sorryAx' in json.dumps(pa): continue
        files.append(e['module'])
        imps = re.findall(r'^import\s+(\S+)', src, re.M)
        gmods = [i for i in imps if i != 'Aeneas' and not i.startswith(('PRV', 'PCV', 'PCQ'))]
        for m in THM.finditer(src):
            name, fresh, gate = m.groups()
            if not okthm.get(name): continue
            credited[name] = gate
            cands = byname.get(gate, [])
            if len(cands) > 1: cands = [c for c in cands if c in gmods] or cands
            if len(cands) == 0: unmatched.append(dict(job=pre, theorem=name, gate=gate, reason='UNMATCHED: definition not in PCXH_PROVENANCE')); continue
            if len(cands) > 1: unmatched.append(dict(job=pre, theorem=name, gate=gate, modules=cands, reason='AMBIGUOUS gate module')); continue
            k = f'{cands[0]}|{gate}'
            if cls[k] in UPGRADABLE:
                changes.append(dict(key=k, was=cls[k], now='EQUALITY_PROVED_JOB', theorem=name, scope=e['attempt'], in_cone=k in cone)); cls[k] = 'EQUALITY_PROVED_JOB'
    # refinement items in STATUS (own class, listed under other)
    for sect in ('proved', 'claims', 'items'):
        for it in status.get(sect, []) if isinstance(status.get(sect), list) else []:
            if str(it.get('status', '')).startswith('LOOP_RETURN_REFINEMENT'):
                mm = re.search(r'\(([^)]+)\)\s*$', it['item']); mod = mm.group(1) if mm else None
                nm = re.sub(r'\s*\([^)]*\)\s*$', '', it['item'])
                th = it.get('theorem')
                if th not in credited_names: unmatched.append(dict(job=pre, item=it['item'], theorem=th, reason='refinement theorem has no exit-0 standard-axioms print_axioms line')); continue
                cand = [k for k in base if mod and k.startswith(mod + '|') and k.endswith('.' + nm)]
                if len(cand) != 1: unmatched.append(dict(job=pre, item=it['item'], reason='UNMATCHED/AMBIGUOUS refinement item', n=len(cand))); continue
                if cls[cand[0]] in UPGRADABLE:
                    changes.append(dict(key=cand[0], was=cls[cand[0]], now='REFINEMENT_LOOP_RETURN', theorem=th, in_cone=cand[0] in cone)); cls[cand[0]] = 'REFINEMENT_LOOP_RETURN'
    for k, v in LEAD.get(pre, {}).items():
        if k not in cls: unmatched.append(dict(job=pre, key=k, reason='UNMATCHED lead classification')); continue
        new = base[k] if v is None else v
        if cls[k] != new:
            changes = [c for c in changes if c['key'] != k]
            if new != base[k]: changes.append(dict(key=k, was=base[k], now=new, theorem='lead classification', scope='lead', in_cone=k in cone))
            cls[k] = new
    after = numbers(cls)
    report.append(dict(job=pre, dir=d, lean_scopes_exit0=scopes_ok, files=files, credited_theorems=len(credited), definition_changes=len(changes),
                       changes_in_cone=sum(1 for c in changes if c['in_cone']), changes=changes, after=after))
pre_demote = numbers(cls); demotions = dict(heartbeat=[], trust_row_withdrawn=[])
if args.demote:
    F = json.load(open(args.demote))
    for d in F['definitions']:
        k = d['definition']
        if d['demote'] and k in cls and cls[k] != 'OPEN': demotions['heartbeat'].append(dict(key=k, was=cls[k], in_cone=k in cone, first_crediting_job=d['first_crediting_job'])); cls[k] = 'OPEN'
    after_hb = numbers(cls)
    for d in F['trust_row_withdrawn']['definitions']:
        k = d['key']
        if k in cls and cls[k] != 'OPEN': demotions['trust_row_withdrawn'].append(dict(key=k, was=cls[k], in_cone=k in cone)); cls[k] = 'OPEN'
        elif k not in cls: demotions['trust_row_withdrawn'].append(dict(key=k, was=None, in_cone=False, note='not in the PCXH baseline universe (non-cone): no count effect'))
    demotions['after_heartbeat_only'] = after_hb
final = numbers(cls)
out = dict(schema='PCXK_COUNTS/1', target_established=False, ref=REF, baseline=dict(source='PCXH_PROVENANCE.json / PCXH_ROW_TABLES.json (P6w)', **b0),
           jobs=[{k: v for k, v in r.items() if k != 'changes'} | {'delta_vs_previous': None} for r in report], final=final,
           headline=dict(settled_of_1707=final['settled'], not_settled_of_1707=final['not_settled'], other_of_1707=final['other'], rows_settled_only_of_599=final['rows_settled_only']),
           changes=[c for r in report for c in r['changes']], unmatched=unmatched, before_demotion=pre_demote, demotions=demotions)
prev = b0
for j, r in zip(out['jobs'], report):
    a = r['after']; j['delta_vs_previous'] = dict(settled=a['settled'] - prev['settled'], not_settled=a['not_settled'] - prev['not_settled'], other=a['other'] - prev['other'], rows_settled_only=a['rows_settled_only'] - prev['rows_settled_only']); prev = a
s = json.dumps(out, indent=1)
if args.out: open(args.out, 'w').write(s + '\n')
print(f"baseline {b0['settled']}/{b0['not_settled']}/{b0['other']} rows {b0['rows_settled_only']}")
for j in out['jobs']: print(j['job'], 'creds', j['credited_theorems'], 'chg', j['definition_changes'], 'in-cone', j['changes_in_cone'], j['delta_vs_previous'])
print('FINAL settled', final['settled'], 'not settled', final['not_settled'], 'other', final['other'], 'rows settled-only', final['rows_settled_only'], 'of 599; unmatched', len(unmatched))
