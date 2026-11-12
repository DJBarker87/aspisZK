#!/usr/bin/env python3
"""X7 gate (vii): every `target_os` site in the five Aspis crates (attribute `cfg`, `cfg_attr`, `cfg!` expression,
manifest `[target.'cfg(..)'.*]` table), for each program whose build contains the crate:
  - whether the deployed build compiles the gated code on the host target (what Charon translates) and on SBF (what
    the deployed ELF contains), from the site's own predicate and every enclosing `cfg` (fv_emit_cfg.py, the resolved
    features of that crate in that program's build, release profile);
  - "difference" when exactly one target compiles it;
  - reached: an LLBC function of that program's emission holds the line (a statement or block inside a reached
    function) or lies inside the gated item (an item that contains reached functions). The LLBC is the host build's,
    so for an SBF-only item outside any function reachability cannot be read from it; such a row says so;
  - what the gated code is: runtime-boundary function (the site lies in a function the config names as a runtime
    boundary: the hash call, the stack-height wrapper), allocator, entry point, test code, build guard
    (compile_error!), import (use), manifest dependency table, or code.
Pass condition: every difference site that a program reaches is a runtime-boundary function, the allocator, the entry
point or test code (imports and build guards hold no code and are listed as such); no reached difference site is
other code; no SBF-only item outside a function is other code. Reads only.
usage: fv_emit_gate_targetos.py <tree> <run dir> <program config.json>...   (TSV on stdout; gate line last)"""
import json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_x1b_llbc import LLBC
from fv_emit_lean import rel, ASPIS_DIRS
import fv_emit_cfg as C

tree, run = Path(sys.argv[1]), Path(sys.argv[2])
progs = []
for cp in sys.argv[3:]:
    cfg = json.loads(Path(cp).read_text())
    label = cfg['program']
    g = LLBC(str(run / label / 'charon' / 'out.llbc'))
    sp = []
    for i, f in g.fun.items():
        s = f['item_meta']['span']; s = s.get('Untagged', s)
        if 'Deduplicated' in s: s = g.HC.get(s['Deduplicated'], s)
        if 'Value' in s: s = s['Value'][1]
        s = s.get('data', s)
        sp.append((rel(g.files.get(s.get('file_id'), '')), (s.get('beg') or {}).get('line') or 0, (s.get('end') or {}).get('line') or 0, g.name[i]))
    llbc_crates = {n.split('::')[0] for n in g.name.values()}
    progs.append(dict(label=label, cfg=cfg, spans=sp, crates=llbc_crates,
                      host=C.features(run / 'tree' / ('%s-host-pkgfeatures.txt' % label)),
                      sbf=C.features(run / 'tree' / ('%s-sbf-pkgfeatures.txt' % label)),
                      pkg_of={d: p for p, d in zip(cfg['packages'], cfg['crate_dirs'])}))
    pr = progs[-1]
    pr['files'] = {(d, t): C.compiled_files(tree, d, pr[t].get(p, set()), t) for p, d in zip(cfg['packages'], cfg['crate_dirs']) for t in ('host', 'sbf')}
pkg_names = {'crates/aspis-core': 'aspis-core', 'crates/aspis-statement': 'aspis-statement', 'crates/aspis-r1-cost-probe': 'aspis-r1-cost-probe',
             'programs/r1-cost-probe': 'aspis-r1-cost-probe-program', 'programs/aspis-pool': 'aspis-pool'}


def fn_extents(b):
    """[(name, first line, last line)] of every `fn` item of a blanked file"""
    out = []
    for m in re.finditer(r'\bfn\s+([A-Za-z_][A-Za-z0-9_]*)', b):
        k = m.end(); depth = 0
        while k < len(b) and not (depth == 0 and b[k] in '{;'):
            depth += {'(': 1, '[': 1, '<': 0, ')': -1, ']': -1}.get(b[k], 0)
            k += 1
        depth = 0
        if k >= len(b) or b[k] == ';':
            continue
        j = k
        while j < len(b):
            if b[j] == '{': depth += 1
            elif b[j] == '}':
                depth -= 1
                if depth == 0: break
            j += 1
        out.append((m.group(1), b.count('\n', 0, m.start()) + 1, b.count('\n', 0, j) + 1))
    return out


def klass(expr, text, gated, enclosing_fns, rb_fns, kind):
    """text: the attribute line through the end of the gated code; gated: the gated code alone"""
    if kind == 'manifest':
        return 'manifest dependency table'
    if set(enclosing_fns) & set(rb_fns):
        return 'runtime-boundary function ' + '/'.join(sorted(set(enclosing_fns) & set(rb_fns)))
    if 'global_allocator' in text or 'BumpAllocator' in gated:
        return 'allocator'
    t = gated.strip()
    if 'entrypoint!' in t:
        return 'entry point'
    if re.search(r'\btest\b', expr):
        return 'test code'
    if t.startswith('compile_error!'):
        return 'build guard (compile_error!)'
    if re.match(r'(pub(\([^)]*\))?\s+)?use\b', t) or re.match(r'(pub(\([^)]*\))?\s+)?extern\s+crate\b', t):
        return 'import (use)'
    if kind == 'cfg_attr':
        return 'attribute only (cfg_attr)'
    return 'code'


OKCLS = ('runtime-boundary function', 'allocator', 'entry point', 'test code', 'build guard', 'import (use)', 'attribute only')
rows, ok = [], True
for d, _crate in ASPIS_DIRS:
    d = d.rstrip('/')
    pkg = pkg_names[d]
    extra = set()
    for pr in progs:
        for (dd, tt), fs in pr['files'].items():
            if dd == d: extra |= {x for x in fs if not x.startswith(d + '/')}
    files = sorted((tree / d).rglob('*.rs')) + sorted(tree / x for x in extra) + [tree / d / 'Cargo.toml']
    for p in files:
        if 'target' in p.relative_to(tree).parts[2:] or not p.exists():
            continue
        rp = str(p.relative_to(tree))
        text = p.read_text(errors='replace')
        if p.suffix == '.toml':
            for k, l in enumerate(text.split('\n')):
                m = re.match(r"\s*\[target\.'cfg\((.*target_os.*)\)'\.([a-z-]*dependencies)\]", l)
                if m:
                    deps = []
                    for l2 in text.split('\n')[k + 1:]:
                        if l2.startswith('['): break
                        mm = re.match(r'\s*([A-Za-z0-9_-]+)\s*=', l2)
                        if mm: deps.append(mm.group(1))
                    rows.append(dict(file=rp, line=k + 1, expr=m.group(1), kind='manifest', a=k + 1, z=k + 1, text='%s: %s' % (m.group(2), ', '.join(deps)), pkg=pkg, deps=deps, text_full='', dir=d))
            continue
        b = C.blank(text)
        L = text.split('\n')
        for line, expr, a, z, inner in C.sites(text):
            if 'target_os' in expr:
                rows.append(dict(file=rp, line=line, expr=expr, kind='cfg', a=a, z=z, text=' '.join(' '.join(L[a - 1:z]).split())[:160], pkg=pkg, text_full='\n'.join(L[line - 1:z]), gated='\n'.join(L[a - 1:z])))
        for m in re.finditer(r'cfg_attr\s*\(([^\]]*target_os[^\]]*)\)\s*\]', b):
            ln = b.count('\n', 0, m.start()) + 1
            rows.append(dict(file=rp, line=ln, expr=text[m.start(1):m.end(1)].split(',')[0], kind='cfg_attr', a=ln, z=ln, text=' '.join(L[ln - 1].split())[:160], pkg=pkg, text_full=L[ln - 1]))
        for m in re.finditer(r'\bcfg!\s*\(', b):
            i = m.end(); depth = 1
            while i < len(b) and depth:
                depth += {'(': 1, ')': -1}.get(b[i], 0); i += 1
            expr = text[m.end():i - 1]
            if 'target_os' in expr:
                ln = b.count('\n', 0, m.start()) + 1
                rows.append(dict(file=rp, line=ln, expr=expr, kind='cfg!', a=ln, z=ln, text=' '.join(L[ln - 1].split())[:160], pkg=pkg, text_full=L[ln - 1]))
        for r in rows:
            if r['file'] == rp and 'fns' not in r:
                r['dir'] = d
                r['fns'] = [n for n, s, e in fn_extents(b) if s <= r['line'] <= e and not (r['a'] <= s and e <= r['z'] and s > r['line'])]
                r['own_fn'] = [n for n, s, e in fn_extents(b) if r['a'] <= s <= r['z']]
                r['inact'] = {}
                for pr in progs:
                    pk = pr['pkg_of'].get(d)
                    if pk is None: continue
                    for t in ('host', 'sbf'):
                        r['inact'][(pr['label'], t)] = [(x, y) for x, y in C.inactive(text, pr[t].get(pk, set()), t) if x != r['line']]
                        r.setdefault('file_on', {})[(pr['label'], t)] = rp in pr['files'][(d, t)]

hdr = ['file', 'line', 'kind', 'cfg', 'gated code', 'class']
for pr in progs:
    hdr += ['%s: host' % pr['label'], '%s: SBF' % pr['label'], '%s: reached' % pr['label'], '%s: verdict' % pr['label']]
print('\t'.join(hdr))
counts = {}
for r in rows:
    r.setdefault('fns', []); r.setdefault('own_fn', [])
    rb = set()
    for pr in progs:
        rb |= set(pr['cfg'].get('runtime_boundary_functions', []))
    cls = klass(r['expr'], r['text_full'] or r['text'], r.get('gated', r['text']), r['fns'], rb, r['kind'])
    out = [r['file'], str(r['line']), r['kind'], r['expr'][:90], r['text'], cls]
    for pr in progs:
        pk = pr['pkg_of'].get(r['dir'])
        if pk is None:
            out += ['-', '-', '-', 'crate not in this program']
            continue
        try:
            ast = C.parse(r['expr'])
        except Exception:
            ast = None
        vals = {}
        for t in ('host', 'sbf'):
            own = C.value(ast, pr[t].get(pk, set()), t) if ast else None
            enc = C.compiled(r.get('inact', {}).get((pr['label'], t), []), r['line'])
            fon = r.get('file_on', {}).get((pr['label'], t), True)
            vals[t] = None if own is None else (own and enc and fon)
        if r['kind'] == 'cfg!':   # an expression: both targets compile the code; the value differs
            vals = {t: (C.value(ast, pr[t].get(pk, set()), t) if ast else None) and r.get('file_on', {}).get((pr['label'], t), True) for t in ('host', 'sbf')}
        if r['kind'] == 'manifest':
            used = sorted(x for x in r.get('deps', []) if x.replace('-', '_') in pr['crates'])
            reached = ('dependency crate in the LLBC: ' + ', '.join(used)) if used else 'no item of the dependency in the LLBC'
            hit = bool(used)
        else:
            hold = [n for f, a, b, n in pr['spans'] if f == r['file'] and ((a <= r['line'] <= b) or (r['a'] <= a <= r['z']))]
            hit = bool(hold)
            if hit:
                reached = 'reached: ' + ', '.join(sorted(set(hold), key=len)[:2])
            elif vals['sbf'] and not vals['host'] and not r['fns']:
                reached = 'SBF-only item outside a function: not readable from the host LLBC'
            else:
                reached = 'not reached'
        if vals['host'] is None or vals['sbf'] is None:
            verdict = 'FAIL: predicate not evaluated'
        elif vals['host'] == vals['sbf']:
            verdict = 'no target difference at the deployed features (%s on both)' % ('compiled' if vals['host'] else 'compiled out')
        elif not hit and not reached.startswith('SBF-only'):
            verdict = 'difference, not reached'
        elif cls.startswith(OKCLS):
            verdict = 'difference, %s: allowed' % ('reached' if hit else 'SBF-only item')
        else:
            verdict = 'FAIL: difference in %s code' % ('reached' if hit else 'SBF-only item')
        ok &= not verdict.startswith('FAIL')
        counts[verdict.split(' (')[0].split(':')[0]] = counts.get(verdict.split(' (')[0].split(':')[0], 0) + 1
        out += ['compiled' if vals['host'] else ('?' if vals['host'] is None else 'out'), 'compiled' if vals['sbf'] else ('?' if vals['sbf'] is None else 'out'), reached, verdict]
    print('\t'.join(x.replace('\t', ' ') for x in out))
print('# sites %d; verdicts (site x program): %s' % (len(rows), json.dumps(counts, sort_keys=True)))
print('# custom cfg flags met (taken as unset): %s' % (', '.join(sorted(C.CUSTOM_FLAGS)) or 'none'))
print('# files compiled from outside the five crate directories (by #[path]): %s' % (', '.join(sorted({x for pr in progs for (dd, tt), fs in pr['files'].items() for x in fs if not any(x.startswith(c + '/') for c in pr['cfg']['crate_dirs'])})) or 'none'))
print('gate (vii) target_os sites: %s' % ('pass' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
