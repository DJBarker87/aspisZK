#!/usr/bin/env python3
"""Aspis freeze emission: cross-scope resolution of external (bodiless) declarations.
For every axiom/opaque in each scope's FunsExternal, class it by the Rust path (std / SDK / Aspis code) and, for
Aspis code, look for a definition with a body under the same Rust path in any scope's Funs, and for that
definition's row in rows-frozen.tsv (translates, elaborates). Reads only."""
import re, sys, json, collections, csv
src, rows_tsv, out = sys.argv[1], sys.argv[2], sys.argv[3]
SC = ['v', 'p', 's', 'd', 'c']
doc = re.compile(r'^/-- \[(.+?)\]:?\s*$')
def norm(p):
    p = re.sub(r'\s+', ' ', p.strip())
    return p
def blocks(path):
    """yield (rust_path, name_pattern, kind, lean_name, first_line_no)"""
    L = open(path).read().split('\n'); i = 0
    while i < len(L):
        m = doc.match(L[i])
        if not m and L[i].startswith('/-- ['):
            # multi-line first doc line
            j = i; buf = L[i]
            while ']:' not in buf and j + 1 < len(L) and j - i < 6: j += 1; buf += ' ' + L[j].strip()
            m = re.match(r'^/-- \[(.+?)\]:', buf)
        if m:
            rp = norm(m.group(1)); pat = None; j = i + 1
            while j < len(L) and '-/' not in L[j - 1] if j > i + 1 else True:
                mm = re.search(r'Name pattern: \[(.+)\]\s*$', L[j])
                if mm: pat = norm(mm.group(1))
                if '-/' in L[j]: j += 1; break
                j += 1
            # declaration line(s) after attributes
            k = j
            while k < len(L) and (L[k].startswith('@[') or L[k].startswith('  "') or L[k].strip() == '' or L[k].startswith('  ')) and not re.match(r'^(axiom|opaque|def|noncomputable|divergent|partial|irreducible_def|abbrev|structure|inductive|instance|theorem)', L[k]): k += 1
            if k < len(L):
                d = re.match(r'^(?:@\[.*?\]\s*)?(noncomputable\s+)?(axiom|opaque|def|abbrev|irreducible_def|instance|divergent def|partial def)\s+(\S+)', L[k])
                if d: yield rp, pat, d.group(2), d.group(3), k + 1
            i = k + 1
        else: i += 1
defs = collections.defaultdict(list)   # rust path -> [(scope, lean name, line)]
exts = []
for s in SC:
    for rp, pat, kind, name, ln in blocks(f'{src}/AspisFRZfrza{s}Funs.lean'):
        if kind in ('axiom', 'opaque'): exts.append((s, 'Funs', rp, pat, name, ln))
        else: defs[rp].append((s, name, ln))
    for rp, pat, kind, name, ln in blocks(f'{src}/AspisFRZfrza{s}FunsExternal.lean'):
        if kind in ('axiom', 'opaque'): exts.append((s, 'FunsExternal', rp, pat, name, ln))
        else: defs[rp].append((s + '-ext', name, ln))
rows = {}
for r in csv.DictReader(open(rows_tsv), delimiter='\t'): rows.setdefault(r['function'], []).append(r)
def cls(rp):
    head = re.sub(r'^\{?impl.*? for ', '', rp)
    first = re.match(r'[\{\s]*(?:impl[^:]*?\s)?([a-z_0-9]+)::', rp)
    c = rp.split('::')[0].lstrip('{')
    for pre in ('aspis_core', 'aspis_statement', 'aspis_r1_cost_probe_program', 'aspis_r1_cost_probe', 'aspis_pool'):
        if re.search(r'(^|[\s<{(\[,&])' + pre + '::', rp): return 'aspis'
    if re.search(r'(^|[\s<{(\[,&])(solana_[a-z_0-9]+|pinocchio[a-z_0-9]*|sha2|five8[a-z_0-9]*|bs58)::', rp): return 'sdk'
    if re.search(r'(^|[\s<{(\[,&])(core|alloc|std)::', rp): return 'std'
    return 'other'
res = []
for s, f, rp, pat, name, ln in exts:
    c = cls(rp); d = defs.get(rp, []); 
    if not d and pat: d = defs.get(pat, [])
    rr = rows.get(rp) or rows.get(pat or '') or []
    res.append(dict(scope=s, file=f, rust=rp, lean=name, line=ln, cls=c, defined_in=[x[0] for x in d], rows=[(r['run'], r['translates'], r['elaborates'], r['class']) for r in rr]))
json.dump(res, open(out, 'w'), indent=1)
by = collections.Counter((r['scope'], r['cls']) for r in res)
print('external declarations per scope and class:'); 
for s in SC: print(' ', s, {c: by[(s, c)] for c in ('aspis', 'sdk', 'std', 'other')})
print('\nAspis-code externals with NO definition with a body in any scope (unique Rust paths):')
seen = collections.OrderedDict()
for r in res:
    if r['cls'] == 'aspis' and not r['defined_in']: seen.setdefault(r['rust'], []).append(r['scope'])
for k, v in seen.items(): print('  ', ''.join(sorted(set(v))), k)
print(f'  -> {len(seen)} paths')
print('\nAspis-code externals that ARE defined in another scope:', len({r['rust'] for r in res if r['cls'] == 'aspis' and r['defined_in']}), 'paths')
bad = collections.OrderedDict()
for r in res:
    if r['cls'] == 'aspis' and r['defined_in']:
        el = [x for x in r['rows'] if x[2] == 'yes']
        if not el: bad.setdefault(r['rust'], (r['defined_in'], r['rows']))
print('  of which the defining row does not elaborate / has no row:')
for k, v in bad.items(): print('   ', k, v)
print('\nSDK externals (unique):')
for k in sorted({r['rust'] for r in res if r['cls'] == 'sdk'}): print('  ', k)
print('\nother (unique):')
for k in sorted({r['rust'] for r in res if r['cls'] == 'other'}): print('  ', k)
print('\nstd externals (unique):', len({r['rust'] for r in res if r['cls'] == 'std'}))
