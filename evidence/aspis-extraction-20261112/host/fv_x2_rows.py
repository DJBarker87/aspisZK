#!/usr/bin/env python3
"""X2: tables of one Pool emission (reads only; run locally on a copy of the run directory fetched from the host).
Row rule: the freeze emission's (fv_frz_emit_run.py make_rows, unchanged): one row per function or constant of a crate
with a doc block in the adapted Funs or FunsExternal; closures, loop bodies, core-trait impl methods and type
declarations are not rows; errors in loop bodies and closures count for their function.
Added per row: crate, source revision, body sha256 in the Pool ledger convention (fv_x2_bodyhash.py), changed against
the pin c7593d23fdc (same convention), Lean module and definition name, overflow-check setting, and for an opaque
item the exact Aeneas message from the exploratory (non-aborting) run that rejected it.
usage: fv_x2_rows.py <run dir> <gaps.json> <bodyhash-frozen.json> <bodyhash-pin.json> <overflow label> <out dir>
  gaps.json: {"<rust path as Aeneas names it>": {"message": ..., "run": ..., "construct": ...}, ...}"""
import collections, json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'aspis-freeze-20261112' / 'host'))
import fv_frz_emit_run as FRZ
RUN, GAPS, BHF, BHP, OVF, OUT = Path(sys.argv[1]), json.load(open(sys.argv[2])), json.load(open(sys.argv[3])), json.load(open(sys.argv[4])), sys.argv[5], Path(sys.argv[6])
REV = BHF['revision']; OUT.mkdir(parents=True, exist_ok=True)
res = json.load(open(RUN / 'result.json')); pre = res['lean_prefix']
funs, ext = RUN / 'lean-src' / (pre + 'Funs.lean'), RUN / 'lean-src' / (pre + 'FunsExternal.lean')
log = (RUN / 'summaries' / ('lean-%sFuns.log' % pre)).read_text(errors='replace')
fexit = res['lean']['Funs']['exit']
aerr = json.load(open(RUN / 'summaries' / 'aeneas-errors-release.json'))
CR = {'aspis_pool': 'programs/aspis-pool/src/', 'aspis_statement': 'crates/aspis-statement/src/', 'aspis_core': 'crates/aspis-core/src/'}
bh = collections.defaultdict(list)
for f in BHF['functions']: bh[f['path']].append(f)
pinkey = collections.defaultdict(list)
for f in BHP['functions']: pinkey[f['key']].append(f['body_sha256'])
def lean_names(path):
    """(rust, file, line) -> Lean definition name, from the doc blocks of an adapted module"""
    out = {}
    if not path.exists(): return out
    L = path.read_text().split('\n')
    for b in FRZ.blocks(path):
        body = '\n'.join(L[b['first'] - 1:b['last']]); body = re.sub(r'(?s)^/--.*?-/\n', '', body)
        m = FRZ.KIND.search(body)
        if m: out.setdefault((b['rust'], b['file'], b['beg']), m.group(2))
    return out
ln_f, ln_x = lean_names(funs), lean_names(ext)
def norm_file(f, crate):
    if not f: return ''
    m = re.search(r'(?:^|/)_root_\.\w+\.(\w+)\.rs$', f)
    if m: return f
    return f if f.startswith(('programs/', 'crates/')) else CR[crate] + f.split('/src/')[-1]
def body_of(path, line, rust):
    if not path or not line: return None
    name = re.sub(r'<.*', '', rust).split('::')[-1]
    c = [f for f in bh.get(path, []) if f['name'] == name and abs(f['start'] - int(line)) <= 3]
    if not c: c = [f for f in bh.get(path, []) if f['start'] <= int(line) <= f['end'] and f['name'] == name]
    return min(c, key=lambda f: abs(f['start'] - int(line))) if c else None
# full Lean error texts per emitted block (closures and loop bodies count for their function)
errblocks = []
for b in re.split(r'(?m)^(?=\S+\.lean:\d+:\d+: error)', log):
    m = re.match(r'(\S+\.lean):(\d+):\d+: error', b)
    if m and m.group(1).endswith(funs.name): errblocks.append((int(m.group(2)), ' '.join(b.split())))
fbl = FRZ.blocks(funs); full = collections.defaultdict(list)
for ln, t in errblocks:
    k = max((i for i, b in enumerate(fbl) if b['first'] <= ln), default=None)
    if k is not None:
        r = fbl[k]['rust']; full[r if fbl[k]['loop'] else FRZ.owner(r)].append(t)
def lean_class(errs):
    cls = set()
    for t in errs:
        if re.search(r'Unknown (constant|identifier)|is not a field of structure', t): cls.add('library item missing from the old library')
        elif re.search(r'wrapping_sh[lr]', t): cls.add('library signature differs in the old library (wrapping_shl/wrapping_shr shift-amount type)')
        elif re.search(r'expected a product type, got\s+core\.ops\.control_flow\.ControlFlow', t): cls.add('library encoding differs in the old library (? on a value that holds a mutable borrow: emitted code expects a backward function from branch)')
        elif re.search(r'Invalid field `pool_v1_vault_token_account_address`', t): cls.add('emitted name shadowed: a local named vault hides the module vault')
        else: cls.add('other: ' + t[t.find('error'):][:160])
    return sorted(cls)
rows = []
for crate in CR:
    rr, other = FRZ.make_rows(crate, funs, ext, log, fexit, aerr, [], False)
    for r in rr:
        path = norm_file(r['file'], crate); k = (r['function'], r['file'], r['line'])
        b = body_of(path, r['line'], r['function'])
        g = GAPS.get(r['function']) or next((v for kk, v in GAPS.items() if kk.replace(' ', '') == r['function'].replace(' ', '')), None)
        if r['translates'].startswith('opaque'):
            tr = 'no: opaque by name (named gap)' if g else 'no: opaque, not a named gap'
        else: tr = r['translates']
        changed = ''
        if b:
            pk = pinkey.get(b['key'])
            changed = 'new (absent at the pin)' if pk is None else ('unchanged' if b['body_sha256'] in pk else 'changed')
        rows.append(dict(path=r['function'], crate=crate, file_line='%s:%s' % (path, r['line'] or ''), rev=REV, body=(b['body_sha256'] if b else ''),
                         key=(b['key'] if b else ''), translates=tr, elaborates=r['elaborates'], module=(pre + 'Funs' if k in ln_f and 'definition' in str(tr) or tr == 'yes' else pre + 'FunsExternal'),
                         lean=(ln_f.get(k) or ln_x.get(k) or ''), overflow=OVF, changed=changed,
                         lean_errors=lean_class(full.get(r['function'], [])) if r['elaborates'].startswith('no') else [],
                         note=('named gap: ' + g['message'] + ((' | construct: ' + g['construct']) if g.get('construct') else '')) if g else ''))
cols = ('rust_path', 'crate', 'file_line', 'source_revision', 'body_sha256', 'ledger_key', 'translates', 'elaborates', 'lean_module', 'lean_name', 'overflow_checks', 'changed_vs_pin_c7593d23fdc', 'lean_error_class', 'note')
with open(OUT / 'rows.tsv', 'w') as f:
    f.write('\t'.join(cols) + '\n')
    for r in rows:
        f.write('\t'.join(('; '.join(r[k]) if isinstance(r[k], list) else str(r[k])).replace('\t', ' ').replace('\n', ' ') for k in ('path', 'crate', 'file_line', 'rev', 'body', 'key', 'translates', 'elaborates', 'module', 'lean', 'overflow', 'changed', 'lean_errors', 'note')) + '\n')
tot = collections.defaultdict(collections.Counter)
for r in rows:
    cat = ('translates and elaborates' if r['elaborates'] == 'yes' else 'translates only') if r['translates'] == 'yes' else ('named gap (opaque)' if 'named gap' in r['translates'] else 'not translated')
    tot[r['crate']][cat] += 1; tot['all'][cat] += 1; tot[r['crate']]['rows'] += 1; tot['all']['rows'] += 1
json.dump({k: dict(v) for k, v in tot.items()}, open(OUT / 'totals.json', 'w'), indent=1)
print(json.dumps({k: dict(v) for k, v in tot.items()}, indent=1))
