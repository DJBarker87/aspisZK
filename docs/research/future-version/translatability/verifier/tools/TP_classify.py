#!/usr/bin/env python3
"""Aspis translatability pass: one classification row per function of the two crates that an emission reaches.
Inputs per scope: the raw emission directory (Funs.lean, FunsExternal_Template.lean), the Aeneas error summary JSON,
the Lean error map JSON (may be absent), plus the status rows of the R1 table and the function-text comparison with
the pin. Output: JSON rows and a Markdown table.
usage: TP_classify.py <out.json> <out.md> <status_rows.json> <fntext.json> <scope-name>=<raw dir>,<aeneas summary>,<errmap or -> ..."""
import json, re, sys
from pathlib import Path
OUTJ, OUTM, STATUS, FNTEXT = sys.argv[1:5]; scopes = sys.argv[5:]
status = json.load(open(STATUS)); fntext = json.load(open(FNTEXT))
def base(n): return n.strip('`').split('::')[-1].split('<')[0]
def blocks(path):
    t = Path(path).read_text() if Path(path).exists() else ''
    for b in re.split(r'(?m)^(?=/-- )', t):
        m = re.match(r"/-- (?:Trait implementation: |Trait declaration: )?\[([^\]]*(?:\][^\]]*)*?)\](:? loop[^\n]*)?:?\n(?:\s+Source: '([^']*)', lines (\d+):\d+-(\d+):\d+)?", b)
        if not m: continue
        kind = re.search(r'(?m)^(?:@\[[^\n]*\]\s*)*(?:noncomputable\s+)?(def|axiom|structure|inductive|instance)\b\s*(\S*)', re.sub(r'(?s)^/--.*?-/\n', '', b))
        lean = (kind.group(2) or '') if kind else ''
        if kind and not lean:
            mm = re.search(r'(?m)^(?:def|axiom)\s*\n\s*(\S+)', b); lean = mm.group(1) if mm else ''
        yield dict(rust=m.group(1), loop=bool(m.group(2)), file=m.group(3), beg=m.group(4), end=m.group(5), kind=kind.group(1) if kind else None, lean=lean,
                   sorry=bool(re.search(r'(?m)^\s*sorry\s*$', b)))
rows = {}
for sc in scopes:
    name, rest = sc.split('=', 1); raw, summ, errmap = rest.split(',')
    errs = json.load(open(summ)) if Path(summ).exists() else {}
    em = json.load(open(errmap)) if errmap != '-' and Path(errmap).exists() else None
    failing = {}
    if em:
        for x in em['failing']: failing[x['lean']] = x['errors'][0]['text']
    for src in ('Funs.lean', 'FunsExternal_Template.lean'):
        for b in blocks(Path(raw) / src):
            r = b['rust']
            if not r.startswith(('aspis_r1_cost_probe', 'aspis_r1_cost_probe_program')): continue
            if not b['file'] or '/src/' not in (b['file'] or '') or b['file'].startswith('/'): 
                if not b['file']: continue
            if re.search(r'\{impl core::|closure|::\{[^}]*core::ops::function', r) or b['kind'] in ('structure', 'inductive', 'instance'): 
                owner = re.sub(r'::\{(?:impl )?core::ops::function.*$', '', r)
                if owner in rows and b['lean'] in failing: rows[owner].setdefault('lean_errors', []).append('closure: ' + failing[b['lean']][:150])
                continue
            key = r
            row = rows.setdefault(key, dict(function=r, file=(b['file'] or '').split('/src/')[-1], line=b['beg'], scopes=[], lean_errors=[]))
            if b['loop']:
                if b['lean'] in failing: row['lean_errors'].append('loop: ' + failing[b['lean']][:150])
                continue
            e = errs.get(r) or next((v for k, v in errs.items() if k.replace(' ', '') == r.replace(' ', '')), None)
            row['scopes'].append(dict(scope=name, emitted=('axiom (opaque or body rejected)' if b['kind'] == 'axiom' else 'placeholder' if b['sorry'] else 'definition'),
                                      aeneas_errors=[x['kind'] + ': ' + x['error'] for x in e] if e else [], lean=('error: ' + failing[b['lean']][:150]) if b['lean'] in failing else ('elaborates' if em and b['kind'] == 'def' and not b['sorry'] else None)))
    # functions named in the Aeneas summary but with no doc block (signature not translated)
    for fn, e in errs.items():
        if fn.startswith('aspis_r1_cost_probe') and '{impl core::' not in fn and 'closure' not in fn:
            row = rows.setdefault(fn, dict(function=fn, file='', line=None, scopes=[], lean_errors=[]))
            if not any(s['scope'] == name for s in row['scopes']):
                row['scopes'].append(dict(scope=name, emitted='nothing', aeneas_errors=[x['kind'] + ': ' + x['error'] for x in e], lean=None))
srow = {}
for f, c in status:
    srow.setdefault((f, base(c[0])), c)
ft = {}
for k, v in fntext.items():
    f, key = k.split('|'); nm = key.split('::')[-1].split('#')[0]
    ft.setdefault((f.split('/src/')[-1], nm), []).append(v['status'])
out = []
for r in sorted(rows.values(), key=lambda r: (r['file'], int(r['line'] or 0))):
    nm = r['function'].split('::')[-1]; f = r['file']
    if not f:
        q = r['function']
        for pre, fl in (('aspis_r1_cost_probe::verifier::candidate::fused::', 'fused.rs'), ('aspis_r1_cost_probe::verifier::candidate::', 'candidate.rs'), ('aspis_r1_cost_probe::verifier::', 'verifier.rs'),
                        ('aspis_r1_cost_probe::r1_semantic::', 'r1_semantic.rs'), ('aspis_r1_cost_probe_program::r1_pool_adapter::owned::', 'r1_pool_adapter_owned.rs'),
                        ('aspis_r1_cost_probe_program::r1_pool_adapter::', 'r1_pool_adapter.rs'), ('aspis_r1_cost_probe_program::', 'lib.rs')):
            if q.startswith(pre): f = r['file'] = fl; break
    c = srow.get((f, nm))
    r['r1_row'] = ('(b) ' + c[2].split(' — ')[0][:70] + ('; SETTLED' if 'provenance SETTLED' in c[2] else '; NOT SETTLED' if 'NOT SETTLED' in c[2] else '') + ' | (c) ' + c[3][:40]) if c else 'no row'
    st = ft.get((f, nm))
    r['pin_text'] = 'not present at the pin' if not st or all(s == 'not present at A' for s in st) else 'yes' if 'identical' in st or 'identical under an added cfg attribute' in st else 'no'
    out.append(r)
json.dump(out, open(OUTJ, 'w'), indent=1)
with open(OUTM, 'w') as md:
    md.write('| Function | Source | Second pair | Lean (second-pair emission) | First pair | R1 row | Text identical to c7593d23fdc |\n|---|---|---|---|---|---|---|\n')
    for r in out:
        def cell(pred):
            ss = [s for s in r['scopes'] if pred(s['scope'])]
            if not ss: return ('not run', '')
            s = ss[0]
            tr = 'translates' if s['emitted'] == 'definition' and not s['aeneas_errors'] else ('NO: ' + '; '.join(dict.fromkeys(x.split(': ', 1)[1] for x in s['aeneas_errors']))[:140]) if s['aeneas_errors'] else s['emitted']
            return (tr, s['lean'] or '')
        t2, l2 = cell(lambda n: n.endswith('T2')); t0, _ = cell(lambda n: n.endswith('T0x'))
        le = l2 or ''
        if r['lean_errors'] and (not le or le == 'elaborates'): le = 'error in a helper: ' + r['lean_errors'][0][:120]
        md.write('| `%s` | %s:%s | %s | %s | %s | %s | %s |\n' % (r['function'].replace('aspis_r1_cost_probe_program::', 'program::').replace('aspis_r1_cost_probe::', ''), r['file'], r['line'], t2, le, t0, 'new gate' if r['pin_text'] == 'not present at the pin' else r['r1_row'], r['pin_text']))
print(len(out), 'rows')
