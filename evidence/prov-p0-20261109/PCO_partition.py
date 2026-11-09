#!/usr/bin/env python3
"""PCO_partition.py: recompute the PRV provenance partition at an arbitrary research revision.

A single-file port of evidence/prov-plan-20261108/PRV_scripts (live, decls, defseg,
scanall, modmap, emods, emods2, classify, final) with every path made a parameter.
Substitutions relative to PRV (all recorded in PCO_CLASSIFICATIONS.json):
  S1 tree/blobs: git objects of --rev (PRV used the f7ccfbace7a tree).
  S2 gate files: --gate-dir/--gate-prefix (PRV used ledger27/NNK_; P0 uses ledger30/NNN_).
  S3 reach lists: root -> REACHABLE.txt.xz chosen as the newest ledger directory that holds one.
  S4 blob->module map for the 336: taken from the PRV_PARTITION blobs list (the map file was not archived).
  S5 pins-hash set: every 64-hex string inside tracked json named *PINS.json, *-pins.json, *EXTRACTION_PINS*.json;
     'frozen' = the file text contains the frozen revision. outside_strict (not archived) is treated as empty.
Usage: PCO_partition.py --rev REV --gate-dir ledger30-20261111 --gate-prefix NNN --scratch DIR --out OUT.json
Run from the evidence/ directory of a checkout that contains the NMH/NML/NKT inputs.
"""
import json, re, sys, os, subprocess, hashlib, collections, lzma, argparse, threading
from multiprocessing import Pool
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
FROZEN_REV = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'

def git(*a, repo=None):
    return subprocess.check_output(['git', *a], cwd=repo)

def uncomment(s):
    out = []; i = 0; depth = 0; string = False
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; out += [' ', ' ']; i += 2
            elif s.startswith('-/', i): depth -= 1; out += [' ', ' ']; i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif string:
            if s[i] == '\\' and i + 1 < len(s): out += [' ', ' ']; i += 2
            elif s[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif s.startswith('/-', i): depth = 1; out += [' ', ' ']; i += 2
        elif s.startswith('--', i):
            end = s.find('\n', i); end = len(s) if end < 0 else end; out.extend(' ' * (end - i)); i = end
        elif s[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(s[i]); i += 1
    assert depth == 0, 'unterminated comment'
    return ''.join(out)

DRX = re.compile(r'(?m)^[ \t]*(?:(namespace)\s+(\S+)|(end)\b(?:[ \t]+(\S+))?|((?:noncomputable[ \t]+)?section)\b(?:[ \t]+\S+)?|(?:@\[[^\]\n]*\][ \t]*)*(?:(?:noncomputable|private|protected|partial|unsafe|nonrec)[ \t]+)*(def|abbrev|structure|inductive|theorem|lemma|opaque|axiom|instance|class)\s+(?:\([^)]*\)\s*)?([^\s({:\[]+))')
def decls(s):
    clean = uncomment(s); scope = []; out = []
    for m in DRX.finditer(clean):
        if m[1]: scope.append(('namespace', m[2]))
        elif m[3]:
            if scope: scope.pop()
        elif m[5]: scope.append(('section', ''))
        else:
            if m[6] == 'instance' and m[7] in (':', 'where'): continue
            ns = '.'.join(x[1] for x in scope if x[0] == 'namespace')
            nm = m[7]
            full = nm[7:] if nm.startswith('_root_.') else (ns + '.' if ns else '') + nm
            out.append((full, m[6]))
    return out

DOCRX = re.compile(r'/--\s*\[([^\]]+)\]:?(.*?)-/', re.S)
def symnorm(sym):
    return re.sub(r'(^|[{<,\s(&])([a-z][a-z0-9_]*)::', lambda m: m.group(1) + 'CRATE::' if m.group(2) not in ('core', 'alloc', 'std') else m.group(0), sym)
def strip_comments(t):
    t = re.sub(r'/-.*?-/', '', t, flags=re.S)
    return re.sub(r'--[^\n]*', '', t)
def segments(text):
    out = []; ms = list(DOCRX.finditer(text))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        body = re.split(r'(?m)^end\b|^namespace\b', text[m.end():end])[0]
        src = re.search(r"Source: '([^']+)'", m.group(2))
        norm = ' '.join(strip_comments(body).split())
        out.append({'sym': m.group(1).strip(), 'symn': symnorm(m.group(1).strip()), 'src': src.group(1) if src else None,
                    'norm_sha': hashlib.sha256(norm.encode()).hexdigest(), 'head': norm[:80]})
    return out

def file_imports(t):
    out = []; prelude = False
    t = re.sub(r'/-.*?-/', '', t, flags=re.S)
    for line in t.splitlines():
        s = line.split('--')[0].strip()
        if not s: continue
        if s == 'prelude': prelude = True; continue
        if s.startswith('import '): out += s[7:].split(); continue
        break
    if not prelude: out.append('Init')
    return sorted(set(out))

class Ctx: pass
C = Ctx()

def batch_cat(oids):
    """Yield (oid, bytes) for each oid using one git cat-file --batch process."""
    oids = list(oids)
    p = subprocess.Popen(['git', 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    def feed():
        for i in oids: p.stdin.write((i + '\n').encode())
        p.stdin.close()
    t = threading.Thread(target=feed); t.start()
    for i in oids:
        hdr = p.stdout.readline().split(); n = int(hdr[2]); data = p.stdout.read(n); p.stdout.read(1)
        yield i, data
    t.join(); p.wait()

def cat_oid(oid):
    return subprocess.run(['git', 'cat-file', '-p', oid], capture_output=True).stdout.decode('utf-8', 'replace')

# ---------------------------------------------------------------- stage: tree index
def stage_tree(a, S):
    ls = git('ls-tree', '-r', '-z', '--full-tree', a.rev).split(b'\0')
    lean = []; rs = []; pins = []; allp = {}
    for row in ls:
        if not row: continue
        meta, path = row.split(b'\t'); path = path.decode(); oid = meta.split()[2].decode()
        allp[path] = oid
        if path.endswith('.lean'): lean.append((oid, path))
        elif path.endswith('.rs'): rs.append((oid, path))
        if re.search(r'(PINS\.json|-pins\.json|EXTRACTION_PINS[^/]*\.json)$', path): pins.append((oid, path))
    with open(f'{S}/all_lean.tsv', 'w') as f:
        for o, p in lean: f.write(o + '\t' + p + '\n')
    with open(f'{S}/all_rs.tsv', 'w') as f:
        for o, p in rs: f.write(o + '\t' + p + '\n')
    fl = git('ls-tree', '-r', '--full-tree', '--name-only', FROZEN_REV).decode().split('\n')
    open(f'{S}/frozen_rs.txt', 'w').write('\n'.join(p for p in fl if p.endswith('.rs') and '/src/' in p) + '\n')
    # pins hashes
    out = {}
    pmap = {o: p for o, p in pins}
    for o, data in batch_cat(list(pmap)):
        t = data.decode('utf-8', 'replace')
        out[pmap[o]] = {'hashes': sorted(set(re.findall(r'\b[0-9a-f]{64}\b', t))), 'frozen': FROZEN_REV in t}
    json.dump(out, open(f'{S}/strictpins_hashes.json', 'w'))
    strict = {}
    rec = sorted(set(oid for p, oid in allp.items() if re.search(r'receipt[^/]*\.json$', p, re.I) and re.search(r'aeneas', p, re.I)))
    for oid, data in batch_cat(rec):
        if len(data) > 5_000_000: continue
        t = data.decode('utf-8', 'replace')
        for h in set(re.findall(r'\b[0-9a-f]{64}\b', t)): strict[h] = {'strict_receipts': True}
    json.dump(strict, open(f'{S}/outside_strict.json', 'w'))
    json.dump(allp, open(f'{S}/tree_paths.json', 'w'))
    print('tree', len(lean), 'lean', len(rs), 'rs', len(pins), 'pins files')

# ---------------------------------------------------------------- stage: ledger / roots
REACH_RX = re.compile(r'^(?:.*/)?(?:[A-Za-z0-9]+_)??(?:FAILURE\d+_)?NEP_(?:proof\d+|fixtures)_(.+)_REACHABLE\.txt\.xz$')
def ledger_order(p):
    m = re.search(r'ledger(\d+)-', p)
    return int(m.group(1)) if m else -1
def stage_ledger(a, S):
    led = json.load(lzma.open(f'{a.gate_dir}/{a.gate_prefix}_LEDGER.json.xz'))
    json.dump(led, open(f'{S}/LEDGER.json', 'w'))
    closed = [r for r in led['rows'] if r['status'] == 'CLOSED']
    roots = collections.defaultdict(set)
    for r in closed:
        for o in r.get('root_owners') or []: roots[o['root']].add(r['row'])
    paths = json.load(open(f'{S}/tree_paths.json'))
    cand = collections.defaultdict(list)
    for p in paths:
        if p.endswith('REACHABLE.txt.xz'):
            m = REACH_RX.match(p)
            if m: cand[m.group(1)].append(p)
    gate_n = ledger_order(a.gate_dir)
    rootfile = {}
    for r in roots:
        L = [p for p in cand.get(r, []) if 'FAILURE' not in p.split('/')[-1] and ledger_order(p) <= gate_n]
        if not L: L = cand.get(r, [])
        # newest ledger directory first; ties by path
        L = sorted(L, key=lambda p: (-ledger_order(p), p))
        rootfile[r] = L
    json.dump({r: sorted(v) for r, v in roots.items()}, open(f'{S}/roots.json', 'w'))
    json.dump(rootfile, open(f'{S}/rootfile.json', 'w'))
    print('closed', len(closed), 'roots', len(roots), 'roots without reach file', sum(1 for r in roots if not rootfile[r]))

# ---------------------------------------------------------------- stage: scanall
def stage_scan(a, S):
    paths = collections.defaultdict(list)
    for l in open(f'{S}/all_lean.tsv'):
        h, p = l.rstrip('\n').split('\t'); paths[h].append(p)
    ids = list(paths)
    p = subprocess.Popen(['git', 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    def feed():
        for i in ids: p.stdin.write((i + '\n').encode())
        p.stdin.close()
    threading.Thread(target=feed).start()
    aen = re.compile(rb'AUTOMATICALLY GENERATED BY AENEAS')
    ann = re.compile(rb"/--? \[[A-Za-z_0-9]+::[^\]]*\][^\n]*\n\s*Source: '")
    out = {}
    for i in ids:
        hdr = p.stdout.readline().split(); n = int(hdr[2]); data = p.stdout.read(n); p.stdout.read(1)
        head = data[:6000].decode('utf-8', 'replace')
        imps = file_imports(head)
        out[i] = {'sha256': hashlib.sha256(data).hexdigest(), 'imports': imps, 'aeneas_header': bool(aen.search(data[:400])),
                  'rust_annotations': len(ann.findall(data)), 'bytes': n, 'paths': paths[i]}
    json.dump(out, open(f'{S}/lean_index.json', 'w'))
    print('index', len(out), sum(1 for v in out.values() if v['aeneas_header']), sum(1 for v in out.values() if v['rust_annotations']))

# ---------------------------------------------------------------- stage: modmap + emods
LIB = ('Init', 'Std', 'Lean', 'Mathlib', 'Aeneas', 'Batteries', 'Qq', 'Aesop', 'ProofWidgets', 'Plausible', 'LeanSearchClient', 'ImportGraph', 'Lake')
def load_scan(a):
    scan = {}
    for l in open(f'{a.gate_dir}/{a.gate_prefix}_LOADED_scan.jsonl'):
        r = json.loads(l); scan[r['module']] = r
    return scan
def stage_modmap(a, S):
    idx = json.load(open(f'{S}/lean_index.json')); scan = load_scan(a)
    proj = {m: r for m, r in scan.items() if m.split('.')[0] not in LIB}
    bymod = collections.defaultdict(set); byimp = collections.defaultdict(set)
    for gid, v in idx.items():
        for p in v['paths']:
            parts = p[:-5].split('/')
            for i in range(len(parts)): bymod['.'.join(parts[i:])].add(gid)
        byimp[tuple(v['imports'])].add(gid)
    res = {}
    for m, r in proj.items():
        oi = tuple(sorted(set(r['imports']))); named = bymod.get(m, set())
        match = [g for g in named if tuple(idx[g]['imports']) == oi]
        shas = sorted(set(idx[g]['sha256'] for g in match)); how = 'path+imports' if shas else None
        if not shas:
            other = list(byimp.get(oi, ())); how = 'imports-only' if other else 'none'
        em = any(idx[g]['aeneas_header'] or idx[g]['rust_annotations'] for g in match)
        res[m] = {'how': how, 'candidates': shas, 'emitted_candidate': em, 'decls': r['declarations']}
    json.dump(res, open(f'{S}/proj_modmap.json', 'w'))
    # emods
    sha2gid = {}
    for g, v in idx.items(): sha2gid.setdefault(v['sha256'], g)
    byimp2 = collections.defaultdict(list)
    for g, v in idx.items():
        if v['aeneas_header'] or v['rust_annotations']: byimp2[tuple(v['imports'])].append(g)
    emods = {}
    for m, v in res.items():
        if v['how'] == 'path+imports':
            if v['emitted_candidate']:
                cands = [s for s in v['candidates'] if idx[sha2gid[s]]['aeneas_header'] or idx[sha2gid[s]]['rust_annotations']]
                emods[m] = {'resolution': 'path+imports', 'candidates': cands, 'nonemitted_candidates': [s for s in v['candidates'] if s not in cands]}
        else:
            oi = tuple(sorted(set(scan[m]['imports']))); ns = m.split('.')[0]; good = set()
            for g in byimp2.get(oi, []):
                if re.search(r'(?m)^namespace ' + re.escape(ns) + r'(\.|\s|$)', cat_oid(g)): good.add(idx[g]['sha256'])
            if good: emods[m] = {'resolution': 'imports+namespace(renamed source)', 'candidates': sorted(good), 'nonemitted_candidates': []}
    print('emods', len(emods), collections.Counter(v['resolution'] for v in emods.values()))
    json.dump(emods, open(f'{S}/emods.json', 'w'))

PRIVRX = re.compile(r'^_private\.(.+?)\.0\.(.+)$')
_W = {}
def work(root):
    emods, names, n2, rf, rev = _W['emods'], _W['names'], _W['n2'], _W['rf'], _W['rev']
    hit = collections.defaultdict(set)
    raw = subprocess.run(['git', 'cat-file', '-p', f'{rev}:{rf[root][0]}'], capture_output=True).stdout
    for line in lzma.decompress(raw).decode('utf-8', 'replace').splitlines():
        n = line.strip()
        if not n: continue
        pm = PRIVRX.match(n)
        if pm:
            if pm[1] in emods: hit[pm[1]].add(pm[2])
            n = pm[2]
        if n in names:
            for m in n2[n]: hit[m].add(n)
            continue
        parts = n.split('.')
        for i in range(len(parts) - 1, 1, -1):
            p = '.'.join(parts[:i])
            if p in names:
                for m in n2[p]: hit[m].add(p)
                break
    return root, {k: sorted(v) for k, v in hit.items()}

def stage_hits(a, S):
    idx = json.load(open(f'{S}/lean_index.json')); sha2gid = {}
    for g, v in idx.items(): sha2gid.setdefault(v['sha256'], g)
    emods = json.load(open(f'{S}/emods.json'))
    for m, v in emods.items():
        sets = []; allnames = set()
        for s in v['candidates']:
            try: d = decls(cat_oid(sha2gid[s]))
            except AssertionError: d = []
            ns = set(n for n, k in d); sets.append(ns); allnames |= ns
        v['strong_names'] = sorted(set.intersection(*sets)) if sets else []
        v['any_names'] = sorted(allnames)
    json.dump(emods, open(f'{S}/emods_decl.json', 'w'))
    n2 = collections.defaultdict(set)
    for m, v in emods.items():
        for n in v['strong_names']: n2[n].add(m)
    roots = json.load(open(f'{S}/roots.json')); rf = json.load(open(f'{S}/rootfile.json'))
    _W.update(emods=emods, names=set(n2), n2=n2, rf=rf, rev=a.rev)
    import multiprocessing
    with multiprocessing.get_context('fork').Pool(8) as p: out = dict(p.map(work, sorted(roots), chunksize=4))
    json.dump(out, open(f'{S}/emod_hits.json', 'w'))
    rel = collections.defaultdict(set); defs = collections.defaultdict(set)
    for r, h in out.items():
        for m, ns in h.items(): rel[m].add(r); defs[m] |= set(ns)
    rows = set(x for m in rel for r in rel[m] for x in roots[r])
    print('emitted modules relied:', len(rel), 'of', len(emods), '; rows relying on any emitted module:', len(rows), '; distinct reached names:', sum(len(v) for v in defs.values()))

# ---------------------------------------------------------------- stage: classify + final
REFRX = re.compile(r'(?i)(ref(erence)?$|_ref$|reference|^n[a-z]{2}_|kit)')
FROZEN_CRATES = {'aspis_core', 'aspis_statement', 'aspis_r1_cost_probe', 'aspis_r1_cost_probe_program', 'aspis_pool', 'r1_cost_probe'}
FROZEN5 = {'aspis_core', 'aspis_statement', 'aspis_r1_cost_probe', 'aspis_r1_cost_probe_program', 'aspis_pool'}
def stage_classify(a, S):
    idx = json.load(open(f'{S}/lean_index.json')); sha2gid = {}; sha2paths = collections.defaultdict(set)
    for g, v in idx.items(): sha2gid.setdefault(v['sha256'], g); sha2paths[v['sha256']] |= set(v['paths'])
    cat_sha = lambda s: cat_oid(sha2gid[s])
    em = json.load(open(f'{S}/emods_decl.json')); hits = json.load(open(f'{S}/emod_hits.json')); roots = json.load(open(f'{S}/roots.json'))
    ext = {e['emitted_file_sha256']: e['origin_status'] for e in json.load(open('emission-audit-20261109/NKT_EXTRACTIONS.json'))}
    nmlp = {b['blob']: b for b in json.load(open('emission-repro2-20261110/NML_PROVENANCE.json'))['blobs']}
    nmlin = {b['blob']: b['source_status'] for b in json.load(open('emission-repro2-20261110/NML_INPUT_MAP.json'))['blobs']}
    inv = {b['blob']: b for b in json.load(open('emission-repro-20261110/NMH_INVENTORY.json'))['blobs']}
    outs = json.load(open(f'{S}/outside_strict.json')); sp = json.load(open(f'{S}/strictpins_hashes.json'))
    frozen_hashes = set(); any_pin_hashes = set()
    for p, v in sp.items():
        any_pin_hashes |= set(v['hashes'])
        if v['frozen']: frozen_hashes |= set(v['hashes'])
    F = collections.defaultdict(set); Fsrc = collections.defaultdict(set)
    fresh = [s for s in sha2gid if s in frozen_hashes and (idx[sha2gid[s]]['aeneas_header'] or idx[sha2gid[s]]['rust_annotations'])]
    for s in fresh:
        for seg in segments(cat_sha(s)):
            F[seg['symn']].add(seg['norm_sha']); Fsrc[seg['symn']].add(s)
    print('fresh frozen emitted files', len(fresh), 'symbols', len(F))
    json.dump({k: sorted(v) for k, v in Fsrc.items()}, open(f'{S}/fresh_symbol_files.json', 'w'))
    json.dump(sorted(fresh), open(f'{S}/fresh_files.json', 'w'))
    def cand_status(s):
        if s in nmlp and nmlp[s]['verdict'].startswith('REPRODUCED'): return 'REPRODUCED'
        if s in ext and ext[s] == 'HASH_LINKED_PIN_RECEIPT': return 'RECEIPTED'
        if s in inv: return 'UNRECEIPTED_INV336'
        if s in outs and outs[s]['strict_receipts']: return 'RECEIPTED'
        if s in any_pin_hashes: return 'RECEIPTED'
        return 'UNRECEIPTED_OUTSIDE'
    rel = collections.defaultdict(set); reached = collections.defaultdict(set)
    for r, h in hits.items():
        for m, ns in h.items(): rel[m].add(r); reached[m] |= set(ns)
    out = {}
    for m, v in em.items():
        cs = v['candidates']; sts = [cand_status(s) for s in cs]; texts = {s: cat_sha(s) for s in cs}; crates = set()
        for s, t in texts.items():
            mm = re.search(r'^-- \[([A-Za-z0-9_]+)\]', t, re.M)
            if mm: crates.add(mm.group(1))
        is_ref = any(REFRX.search(c) for c in crates) or bool(re.search(r'(Ref|Reference)(\b|_|$)', m))
        if crates & FROZEN_CRATES and not is_ref: kind = 'FROZEN_CRATE'
        elif is_ref: kind = 'REFERENCE'
        elif crates: kind = 'PROBE_OR_CUT_CRATE'
        else: kind = 'TRANSFORMED_COPY'
        segs_by_cand = {}
        for s, t in texts.items():
            nsm = re.search(r'(?m)^namespace (\S+)', t); nsp = nsm.group(1) if nsm else ''; L = []
            for seg in segments(t):
                hm = re.search(r'\b(?:def|abbrev|structure|inductive|opaque|axiom|theorem|instance)\s+(\S+)', seg['head'])
                seg['lean'] = (nsp + '.' if nsp else '') + hm.group(1) if hm else None
                L.append(seg)
            segs_by_cand[s] = L
        rset = reached.get(m, set()); defs = {}
        for s, L in segs_by_cand.items():
            for seg in L:
                if seg['lean'] in rset:
                    d = defs.setdefault(seg['lean'], {'symn': seg['symn'], 'src': seg['src'], 'shas': set()}); d['shas'].add(seg['norm_sha'])
        cover = collections.Counter()
        for n, d in defs.items():
            if d['symn'] not in F: d['cov'] = 'UNCOVERED'
            elif d['shas'] <= F[d['symn']]: d['cov'] = 'IDENTICAL'
            elif d['shas'] & F[d['symn']]: d['cov'] = 'IDENTICAL_SOME_VERSION'
            else: d['cov'] = 'COVERED_DIFFERS'
            cover[d['cov']] += 1
        o = {'kind': kind, 'crates': sorted(crates),
             'candidates': [{'sha256': s, 'status': st, 'paths': sorted(sha2paths[s])[:3], 'nml_source_status': nmlin.get(s)} for s, st in zip(cs, sts)],
             'relied': m in rel, 'roots': sorted(rel.get(m, ())), 'rows': sorted(set(x for r in rel.get(m, ()) for x in roots[r])),
             'reached_names': len(rset), 'reached_emitted_defs': len(defs), 'coverage': dict(cover),
             'defs': {n: {'symn': d['symn'], 'src': d['src'], 'cov': d['cov']} for n, d in defs.items()}}
        stt = set(x['status'] for x in o['candidates'])
        o['prov'] = 'RECEIPTED' if stt <= {'RECEIPTED', 'REPRODUCED'} else ('MIXED' if stt & {'RECEIPTED', 'REPRODUCED'} else 'UNRECEIPTED')
        out[m] = o
    json.dump(out, open(f'{S}/classified.json', 'w'), indent=0)
    c = collections.Counter((o['relied'], o['prov'], o['kind']) for o in out.values())
    for k, n in sorted(c.items(), key=lambda x: (-x[0][0], -x[1])): print(n, k)

def stage_final(a, S):
    o = json.load(open(f'{S}/classified.json')); roots = json.load(open(f'{S}/roots.json'))
    base = json.load(open(a.baseline)); bm = {b['blob']: [b['module']] for b in base['blobs']}
    inv = {b['blob']: b for b in json.load(open('emission-repro-20261110/NMH_INVENTORY.json'))['blobs']}
    nml = {b['blob']: b for b in json.load(open('emission-repro2-20261110/NML_PROVENANCE.json'))['blobs']}
    led = json.load(open(f'{S}/LEDGER.json')); closed = sorted(r['row'] for r in led['rows'] if r['status'] == 'CLOSED')
    fmods = set()
    for l in open(f'{S}/frozen_rs.txt'):
        l = l.strip()
        if not l: continue
        p = l.split('/src/', 1)[1][:-3]; parts = p.split('/')
        if parts[-1] in ('mod', 'lib'): parts = parts[:-1]
        for i in range(len(parts)): fmods.add('::'.join(parts[i:]))
    def frozen_mappable(symn):
        p = re.sub(r'\{[^{}]*\}', '', re.sub(r'\{[^{}]*\}', '', symn)).replace('CRATE::', '')
        parts = [x for x in p.split('::') if x]
        for k in range(len(parts) - 1, 0, -1):
            for i in range(k):
                if '::'.join(parts[i:k]) in fmods: return True
        return len(parts) <= 1
    rs_by_dir = collections.defaultdict(list)
    for l in open(f'{S}/all_rs.tsv'):
        g, p = l.rstrip('\n').split('\t'); parts = p.split('/')
        if 'evidence' in parts:
            i = parts.index('evidence'); rs_by_dir['/'.join(parts[:i + 2])].append((g, p))
    def jobdir(p):
        parts = p.split('/')
        if 'evidence' in parts: i = parts.index('evidence'); return '/'.join(parts[:i + 2])
    def ref_source(v):
        st = [c.get('nml_source_status') for c in v['candidates']]
        if any(s in ('RECOVERED_HASH_LINKED_INPUT', 'RECOVERED_LLBC_LINKED_PACKAGE') for s in st): return 'b1_committed_hash_linked'
        names = set()
        for n, d in v['defs'].items():
            last = re.sub(r'\{[^{}]*\}', '', d['symn']).split('::')[-1]
            if last: names.add(last)
        found = False
        for c in v['candidates']:
            for p in c['paths']:
                jd = jobdir(p)
                if not jd: continue
                for g, rp in rs_by_dir.get(jd, [])[:400]:
                    t = cat_oid(g)
                    if any(re.search(r'\bfn\s+' + re.escape(n) + r'\b', t) for n in names): found = rp; break
                if found: break
            if found: break
        return ('b2_committed_not_linked:' + found) if found else 'b3_source_not_found'
    mods = {}
    for m, v in o.items():
        rec = {'module': m, 'kind': v['kind'], 'crates': v['crates'], 'prov': v['prov'], 'relied': v['relied'], 'n_rows': len(v['rows']), 'rows': v['rows'],
               'n_roots': len(v['roots']), 'reached_emitted_defs': v['reached_emitted_defs'], 'coverage': v['coverage'], 'candidates': v['candidates']}
        if not v['relied']: g = 'd'; sub = 'd_no_CLOSED_root_reaches'
        elif v['prov'] == 'RECEIPTED': g = 'R'; sub = 'receipted_or_reproduced'
        elif v['prov'] == 'MIXED': g = 'a'; sub = 'a_pending_live_version_is_receipted_or_copy'
        elif v['kind'] == 'REFERENCE' and not (set(v['crates']) & FROZEN5): g = 'b'; sub = ref_source(v)
        else:
            n = v['reached_emitted_defs']; cov = v['coverage']; ident = cov.get('IDENTICAL', 0) + cov.get('IDENTICAL_SOME_VERSION', 0)
            if n > 0 and ident == n: g = 'a'; sub = 'a_identical_to_fresh_frozen_receipted_emission'
            elif n == 0: g = 'c'; sub = 'c0_no_annotated_definition_reached_manual_mapping'
            elif cov.get('UNCOVERED', 0) == 0: g = 'c'; sub = 'c1_extraction_exists_equality_needed'
            else: g = 'c'; sub = 'c2_new_extraction_and_equality'
            rec['uncovered_not_frozen_mappable'] = len([d for d in v['defs'].values() if d['cov'] == 'UNCOVERED' and not frozen_mappable(d['symn'])])
        rec['group'] = g; rec['subgroup'] = sub
        rec['reached_definitions'] = {n: {'rust': d['symn'], 'source': d['src'], 'coverage': d['cov']} for n, d in v['defs'].items()}
        mods[m] = rec
    blobs = []
    for b, ms in bm.items():
        m = ms[0]; r = mods.get(m); live = r and any(c['sha256'] == b for c in r['candidates'])
        if r is None: g, sub = 'd', 'd_module_not_emitted_candidate'
        elif not r['relied']: g, sub = 'd', 'd_module_not_reached_by_CLOSED_root'
        elif not live: g, sub = 'd', 'd_superseded_version_not_compiled_into_gate'
        elif nml[b]['verdict'].startswith('REPRODUCED'): g, sub = 'a', 'a_reproduced_NMH_NML'
        else: g, sub = r['group'], r['subgroup']
        if g == 'R': g, sub = 'a', 'a_module_live_version_receipted'
        blobs.append({'blob': b, 'module': m, 'group': g, 'subgroup': sub, 'nml_verdict': nml[b]['verdict'], 'paths': inv[b]['paths'][:2], 'module_rows': r['n_rows'] if r else 0})
    def rows_of(pred): return sorted(set(x for r in mods.values() if pred(r) for x in r['rows']))
    R_c = rows_of(lambda r: r['group'] == 'c'); R_b3 = rows_of(lambda r: r['subgroup'] == 'b3_source_not_found')
    R_b2 = rows_of(lambda r: r['subgroup'].startswith('b2')); R_ap = rows_of(lambda r: r['subgroup'] == 'a_pending_live_version_is_receipted_or_copy')
    R_at = rows_of(lambda r: r['subgroup'] == 'a_identical_to_fresh_frozen_receipted_emission'); R_any = rows_of(lambda r: r['relied'] and r['group'] != 'R')
    summ = {'blob_groups': dict(collections.Counter(x['group'] for x in blobs)), 'blob_subgroups': dict(collections.Counter(x['subgroup'] for x in blobs)),
            'module_groups': dict(collections.Counter(r['group'] for r in mods.values())), 'module_subgroups': dict(collections.Counter(r['subgroup'] for r in mods.values()))}
    rootless = sorted(r['row'] for r in led['rows'] if r['status'] == 'CLOSED' and not (r.get('root_owners')))
    summ['rows'] = {'closed': len(closed), 'rootless': rootless, 'any_unreceipted_emitted_module': len(R_any), 'c': len(R_c),
                    'c_or_b_unlinked': len(set(R_c) | set(R_b2) | set(R_b3)), 'c_or_b_unlinked_or_a_pending': len(set(R_c) | set(R_b2) | set(R_b3) | set(R_ap)),
                    'a_trivial_only': len(set(R_at) - set(R_c) - set(R_b2) - set(R_b3) - set(R_ap))}
    summ['defs'] = {}
    for g in ['c0_no_annotated_definition_reached_manual_mapping', 'c1_extraction_exists_equality_needed', 'c2_new_extraction_and_equality']:
        cv = collections.Counter()
        for r in mods.values():
            if r['subgroup'] == g:
                for k, x in r['coverage'].items(): cv[k] += x
        summ['defs'][g] = dict(cv)
    summ['c_modules_uncovered_not_frozen_mappable'] = sum(1 for r in mods.values() if r['group'] == 'c' and r.get('uncovered_not_frozen_mappable'))
    res = {'schema': 1, 'target_established': False, 'basis': {'ledger': f'{a.gate_dir}/{a.gate_prefix}_LEDGER.json.xz', 'gate_environment': f'{a.gate_prefix}_LOADED_scan.jsonl',
           'research_revision': a.rev, 'frozen_revision': FROZEN_REV, 'closed_rows': len(closed)},
           'summary': summ, 'rows_affected_c': R_c, 'rows_affected_c_or_b_unlinked': sorted(set(R_c) | set(R_b2) | set(R_b3)), 'rows_affected_c_or_b_unlinked_or_a_pending': sorted(set(R_c) | set(R_b2) | set(R_b3) | set(R_ap)),
           'blobs': blobs, 'modules': mods}
    json.dump(res, open(a.out, 'w'), indent=0)
    print(json.dumps(summ, indent=1))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rev', required=True); ap.add_argument('--gate-dir', required=True); ap.add_argument('--gate-prefix', required=True)
    ap.add_argument('--scratch', required=True); ap.add_argument('--out', required=True)
    ap.add_argument('--baseline', default='prov-plan-20261108/PRV_PARTITION.json')
    ap.add_argument('--stages', default='tree,ledger,scan,modmap,hits,classify,final')
    a = ap.parse_args(); S = a.scratch; os.makedirs(S, exist_ok=True)
    a.rev = git('rev-parse', a.rev).decode().strip()
    for st in a.stages.split(','):
        print('== stage', st, flush=True); globals()['stage_' + {'tree': 'tree', 'ledger': 'ledger', 'scan': 'scan', 'modmap': 'modmap', 'hits': 'hits', 'classify': 'classify', 'final': 'final'}[st]](a, S)
if __name__ == '__main__': main()
