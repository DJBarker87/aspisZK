import json, re, subprocess, sys, glob, os, hashlib, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from PCXI_lib import *
R = '/Users/dominic/ZK/.worktrees/pc-prov-p6y'
FROZEN = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def show(p, rev='HEAD'):
    return subprocess.run(['git', '-C', R, 'show', rev + ':' + p], capture_output=True).stdout
def jshow(p): return json.loads(show(p))
files = set(subprocess.run(['git', '-C', R, 'ls-tree', '-r', '--name-only', 'HEAD'], capture_output=True, text=True).stdout.split('\n'))
P = jshow('evidence/prov-p6u-20261110/PCXF_PROVENANCE.json')
O = jshow('evidence/prov-p0-20261109/PCO_PARTITION.json')
SR = jshow('evidence/prov-p6u-20261110/PCXF_SOURCE_REVISION_AUDIT.json')
SPEC = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'PCXI_SPEC.json')))
pin = {(r['module'], r['definition']): r for r in SR['records']}
sel = []
for mn, mm in P['modules'].items():
    for dn, r in mm['definitions'].items():
        if r.get('in_splitB_cone') and r['status'] == 'RECEIPTED' and mn != 'AspisR1SelectedMaskProbe.Funs':
            pr = pin.get((mn, dn), {})
            if pr.get('verdict', '').startswith('FROZEN_TREE_CRATE_PIN_NAMES_FROZEN_DEFINITION_IDENTICAL'): continue
            sel.append((mn, dn))
# frozen text
ls = subprocess.run(['git', '-C', R, 'ls-tree', '-r', '--name-only', FROZEN], capture_output=True, text=True).stdout.split('\n')
frs = [f for f in ls if f.endswith('.rs') and f.startswith(('crates/', 'programs/'))]
ftext = {f: show(f, FROZEN).decode('utf8', 'replace') for f in frs}
fsha = {f: hashlib.sha256(ftext[f].encode()).hexdigest() for f in frs}
fsha_rev = collections.defaultdict(list)
for f, s in fsha.items(): fsha_rev[s].append(f)
def guess_kind(mod, name):
    if mod.endswith('.Types') or mod.endswith('_Types'): return ['type', 'fn', 'const']
    if re.fullmatch(r'[A-Z][A-Z0-9_]*', name): return ['const', 'type', 'fn']
    if re.fullmatch(r'[A-Z][A-Za-z0-9]*', name): return ['type', 'const', 'fn']
    return ['fn', 'const', 'type']
def find_in(texts, kinds, name, owner):
    for k in kinds:
        for src, t in texts:
            r = find_items(t, k, name, owner)
            if r: return k, src, r
        if owner:
            for src, t in texts:
                r = find_items(t, k, name, None)
                if r: return k, src, r
    return None, None, []
_ff = {}
def frozen_find(kinds, name, owner, hint_mod):
    key = (tuple(kinds), name, owner)
    if key in _ff: return _ff[key]
    out = []
    cand = {f: t for f, t in ftext.items() if name in t}
    for k in kinds:
        for f, t in cand.items():
            r = find_items(t, k, name, owner) or (find_items(t, k, name, None) if owner else [])
            for x in r: out.append((k, f, x))
        if out: break
    _ff[key] = out
    return out
def receipt_env(rpath):
    try: d = json.loads(show(rpath))
    except Exception: return None
    env = d.get('env', {})
    return dict(source_revision=d.get('source_revision'), dirty=d.get('source_tree_dirty'),
                overflow=env.get('CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS'), rustflags=env.get('RUSTFLAGS'),
                cmd=d.get('command'), exit=d.get('exit_status'), receipt=rpath)
records = []
cache_src = {}
def load_src(p):
    if p not in cache_src: cache_src[p] = show(p).decode('utf8', 'replace')
    return cache_src[p]
mods_info = {}
for mn in sorted({m for m, _ in sel}):
    sp = SPEC.get(mn, {})
    texts = [(p, load_src(p)) for p in sp.get('src', []) if p in files]
    for p, ex in sp.get('src_verified', []):
        if p in files and hashlib.sha256(show(p)).hexdigest() == ex: texts.append((p, load_src(p)))
    pinned = {}
    for pf in sp.get('pinned_frozen', []):
        try: d = jshow(pf)
        except Exception: continue
        def walk(o, pre=''):
            if isinstance(o, dict):
                for k, v in o.items():
                    if isinstance(v, str) and re.fullmatch(r'[0-9a-f]{64}', v) and k.endswith('.rs'): yield k, v
                    elif isinstance(v, dict) and isinstance(v.get('sha256'), str) and k.endswith('.rs'): yield k, v['sha256']
                    else: yield from walk(v)
        for k, v in walk(d):
            if k in fsha and fsha[k] == v: pinned[k] = v
    for k in pinned: texts.append(('FROZEN:' + k, ftext[k]))
    rec = [receipt_env(r) for r in sp.get('receipts', []) if r in files]
    for cf in sp.get('config_files', []):
        try:
            d = jshow(cf); e = d.get('env', d)
            rec.append(dict(source_revision=d.get('source_revision') or d.get('revision') or d.get('proof_worktree_head') or d.get('worktree_revision'), dirty=None, overflow=e.get('CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS'), rustflags=None, cmd=None, exit=None, receipt=cf))
        except Exception: pass
    mods_info[mn] = dict(spec=sp, texts=texts, receipts=[x for x in rec if x], pinned=pinned)
for mn, dn in sel:
    mi = mods_info[mn]; sp = mi['spec']
    cr = P['modules'][mn]['definitions'][dn]
    rd = O['modules'][mn]['reached_definitions'].get(dn) or {}
    rp = rd.get('rust') or ''
    owner, name, segs, closure = parse_rust_path(rp)
    arith = cr['arithmetic_class']
    rec = dict(module=mn, definition=dn, rust_path=rp, pco_coverage=rd.get('coverage'), arithmetic_class=arith, previous_status='RECEIPTED',
               crate=O['modules'][mn]['crates'], candidate_sha256=[c['sha256'] for c in O['modules'][mn]['candidates']],
               receipt_files=[r['receipt'] for r in mi['receipts']], source_files=[p for p, _ in mi['texts'] if not p.startswith('FROZEN:')], frozen_files_pinned_equal=sorted(mi['pinned']))
    rec['receipt_revision'] = sorted({str(r['source_revision']) for r in mi['receipts']})
    rec['receipt_tree_dirty'] = sorted({str(r['dirty']) for r in mi['receipts']})
    ov = sorted({str(r['overflow']) for r in mi['receipts']})
    rec['overflow_checks_env'] = ov
    rec['configuration_evidence'] = sp.get('config_note')
    cfg = sp.get('config') or ('ON' if ov == ['true'] else ('UNKNOWN' if mi['receipts'] else 'NO_RECEIPT'))
    rec['configuration'] = cfg
    kinds = guess_kind(mn, name)
    if not name or not mi['texts']:
        rec.update(verdict='NOT_REDERIVABLE', reason=sp.get('why_no_source', 'no Rust source for the receipted extraction found in the repository'))
        records.append(rec); continue
    k, src, items = find_in(mi['texts'], kinds, name, owner)
    if not items:
        rec.update(verdict='NOT_REDERIVABLE', reason='item %s not found in receipt Rust sources %s' % (name, [p for p, _ in mi['texts']][:3]))
        records.append(rec); continue
    rtext = norm(items[0]); rec['receipt_item_file'] = src; rec['receipt_item_kind'] = k; rec['receipt_item_sha256'] = hashlib.sha256(rtext.encode()).hexdigest()
    rec['receipt_item_candidates'] = len(items)
    # frozen
    fi = frozen_find([k], name, owner, segs)
    eq = [(fk, ff) for fk, ff, x in fi if norm(x) == rtext]
    if eq:
        rec['frozen_item_file'] = eq[0][1]; rec['frozen_item_sha256'] = rec['receipt_item_sha256']; rec['text'] = 'EQUAL'
        # local callee closure
        cal = calls(items[0]) - {name}
        dep = []
        alltxt = mi['texts']
        for c in sorted(cal):
            kk, ss, it = find_in(alltxt, ['fn'], c, None)
            if not it: continue
            ff = frozen_find(['fn'], c, None, segs)
            same = any(norm(x) == norm(it[0]) for _, _, x in ff)
            dep.append(dict(callee=c, defined_in=ss, equal_to_frozen=same, frozen_candidates=len(ff)))
        for idn in sorted(set(re.findall(r'\b([A-Z][A-Za-z0-9_]*)\b', items[0])) - {name, 'Self', 'Some', 'None', 'Ok', 'Err', 'Option', 'Result', 'Vec', 'Box', 'Default'}):
            for kk in (['const'] if re.fullmatch(r'[A-Z][A-Z0-9_]*', idn) else ['type']):
                k2, s2, it = find_in(alltxt, [kk], idn, None)
                if not it: continue
                ff = frozen_find([kk], idn, None, segs)
                same = any(norm(x) == norm(it[0]) for _, _, x in ff)
                dep.append(dict(callee=idn, kind=kk, defined_in=s2, equal_to_frozen=same, frozen_candidates=len(ff)))
        rec['local_dependencies'] = dep
        bad = [d for d in dep if not d['equal_to_frozen']]
        if rec['pco_coverage'] == 'COVERED_DIFFERS' and not bad:
            rec.update(verdict='TEXT_DIFFERS', subtype='EMISSION_DIFFERS_FROM_FRESH_FROZEN', reason='Rust item text equals frozen (config %s) but the receipted Lean emission differs from the fresh 4bb3b3f emission (PCO COVERED_DIFFERS); the receipted emission is not shown to translate the frozen text with the frozen tools, so it is not credited as pin-equal' % cfg)
        elif bad:
            rec.update(verdict='TEXT_DIFFERS', subtype='DEPENDENCY_CONTEXT_DIFFERS', reason='item text equals the frozen text but local callee(s) %s differ from or lack a frozen counterpart' % [d['callee'] for d in bad])
        elif arith == 'NO_ARITHMETIC' or cfg == 'ON':
            rec.update(verdict='PIN_EQUAL', reason='item text equals frozen after whitespace/comment normalisation; ' + ('no overflow-sensitive operator (NO_ARITHMETIC), configuration immaterial' if arith == 'NO_ARITHMETIC' else 'receipt overflow checks ON'))
        elif cfg == 'OFF':
            rec.update(verdict='TEXT_DIFFERS', subtype='CONFIG_DIFFERS', reason='text equal but extraction configuration has overflow checks OFF; gate requires checked ON')
        else:
            rec.update(verdict='NOT_REDERIVABLE', subtype='CONFIG_NOT_PINNED', reason='text equal; arithmetic class %s and overflow configuration %s not re-derivable' % (arith, cfg))
    else:
        rec['text'] = 'DIFFERS' if fi else 'NO_FROZEN_COUNTERPART'
        if fi:
            a = rtext; b = norm(fi[0][2]); i = 0
            while i < min(len(a), len(b)) and a[i] == b[i]: i += 1
            rec['first_difference'] = dict(offset=i, receipt=a[max(0, i - 40):i + 80], frozen=b[max(0, i - 40):i + 80], frozen_file=fi[0][1])
            rec.update(verdict='TEXT_DIFFERS', subtype='TEXT', reason='item text differs from every frozen item of that name (%d candidates)' % len(fi))
        else:
            rec.update(verdict='TEXT_DIFFERS', subtype='NO_FROZEN_COUNTERPART', reason='no %s named %s in the frozen crates and programs at 4bb3b3f' % (k, name))
    records.append(rec)
c = collections.Counter(r['verdict'] for r in records)
cs = collections.Counter((r['module'], r['verdict'], r.get('subtype')) for r in records)
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'PCXI_RECEIPTS_raw.json')
json.dump(dict(counts=dict(c), records=records), open(out, 'w'), indent=1)
print(dict(c))
for k, v in sorted(cs.items(), key=lambda x: str(x)): print(k, v)
