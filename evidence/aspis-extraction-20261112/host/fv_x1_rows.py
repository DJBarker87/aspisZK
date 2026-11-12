#!/usr/bin/env python3
"""X1 table builder. Reads only (one finished emission run, optionally a second run at the other overflow setting, the
FRZE-frza per-scope emission, the pin tree and the frozen source). Writes the tables into <table dir>.
usage: fv_x1_rows.py <run dir> <other-setting run dir or -> <table dir>
Tables:
  rows.tsv          one row per function or constant of the four Aspis crates in the emission (the row rule of
                    fv_frz_emit_run.py: a doc block in Funs or FunsExternal; closures, loop bodies, core-trait impl
                    methods and type declarations are not rows; their Lean errors count for the owning function)
  externals.tsv     every bodiless declaration of the package (FunsExternal axioms and TypesExternal opaque types)
  not-emitted.tsv   per crate, every function declaration with a body in the LLBC that has no emitted definition,
                    with the reason found
  compare-frza.tsv  per function present in both: the X1 body at the setting the frza scope used against the frza body,
                    after normalising namespaces and qualified names
  overflow-diff.tsv per function: X1 at overflow checks off against X1 at overflow checks on
  summary.json      totals and checks"""
import bisect, collections, hashlib, json, re, sys
from pathlib import Path
W = Path('/home/dombarker/project-offloads/future-version-20261111')
sys.path.insert(0, str(W / 'frz-emit' / 'bin'))
import fv_frz_emit_run as F          # the freeze driver's row rule (make_rows, classify, blocks), imported read only
FRZA = W / 'frz-emit' / 'frza'
SRC = W / 'src-frz-a'
PIN = W / 'frz-emit' / 'pin-c7593d23fdc'
REV = '3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de'
CRATES = ['aspis_r1_cost_probe_program', 'aspis_r1_cost_probe', 'aspis_statement', 'aspis_core']
CRATE_DIR = {'aspis_r1_cost_probe_program': 'programs/r1-cost-probe/src', 'aspis_r1_cost_probe': 'crates/aspis-r1-cost-probe/src',
             'aspis_statement': 'crates/aspis-statement/src', 'aspis_core': 'crates/aspis-core/src'}
FRZA_SCOPES = {'v': ('aspis_r1_cost_probe', 'AspisTPv', 'on'), 'p': ('aspis_r1_cost_probe_program', 'AspisTPp', 'off'),
               's': ('aspis_statement', 'AspisTP2g', 'on'), 'd': ('aspis_statement', 'AspisTP3stmt', 'on'), 'c': ('aspis_core', 'AspisTP3core', 'on')}
# Named gaps: the items opaque in the primary emission, with the exact rejection of the exploratory run explore1 (no
# item opaque, Aeneas without -abort-on-error; log runs/explore1/runs/A-noabort/aeneas.log), and the two items that are
# not in the primary emission at all.
GAPS = [
 dict(match=r'::deployment_ids::deployment_id$', reason="Aeneas: 'Internal error, please file an issue' at programs/r1-cost-probe/src/deployment_ids.rs 50:15-50:20 (interp/Interp.ml line 686); opaque by flag; called only by the initializers of the statics AUDIT_POOL_PROGRAM and AUDIT_REGISTRY_PROGRAM"),
 dict(match=r'::deployment_ids::program_id$', row='aspis_r1_cost_probe_program::r1_pool_adapter::deployment_ids::program_id', file='programs/r1-cost-probe/src/deployment_ids.rs', line='3', end='44',
      reason="Aeneas: 'Early returns inside of loops are not supported yet' at programs/r1-cost-probe/src/deployment_ids.rs 3:0-44:1 (PrePasses.ml line 575); not in the primary emission (reached only through deployment_id, which is opaque)"),
 dict(match=r'::r1_pool_adapter::close_checkpoint$', reason="Aeneas: 'Inconsistent projection: pe PtrMetadata' on a shared borrow of [AccountInfo] at programs/r1-cost-probe/src/r1_pool_adapter.rs 1033:8-1033:26 (the slice pattern let [checkpoint, base] = accounts; interp/Interp.ml line 686); opaque by flag"),
 dict(match=r'::r1_pool_adapter::lifecycle_accounts$', reason="Aeneas: 'Inconsistent projection: pe PtrMetadata' on a shared borrow of [AccountInfo] at programs/r1-cost-probe/src/r1_pool_adapter.rs 251:8-251:27 (the slice pattern let [target, authority] = accounts; interp/Interp.ml line 686); opaque by flag"),
 dict(match=r'CM31\}::inv$', reason="Aeneas: 'Invalid input for unop: fn_def_to_fn_ptr on aspis_core::field::{aspis_core::field::M31}::inv' at crates/aspis-core/src/field.rs 391:22-391:30 (interp/Interp.ml line 686); opaque by flag aspis_core::field::_::inv; soundness lead's ruling: the first-pair definitions are reused, source text identical to the pin c7593d23fdc (lines 390-392 sha256 f845f645286ccf2e30b22527687ed4c306dbed5696523ac55640ffa6f43075b8)"),
 dict(match=r'CM31\}::inv_with$', row='aspis_core::field::{aspis_core::field::CM31}::inv_with', file='crates/aspis-core/src/field.rs', line='396', end='404',
      reason="Aeneas: 'Arrow types are not supported yet' in the signature at crates/aspis-core/src/field.rs 396:4-396:58 (symbolic/SymbolicToPureTypes.ml line 422) and 'Function pointers are not supported yet' at 398:23-398:36; not in the primary emission (reached only through CM31::inv); soundness lead's ruling: first-pair definition reused, source text identical to the pin c7593d23fdc (lines 396-404 sha256 8f8ae1ea96a589ae88feef7e2cba53c7d01dd9b85f564d63833986c918c09232)"),
 dict(match=r'\{aspis_core::field::M31\}::inv$', reason="no rejection: explore1 translates it; opaque only because this Charon cannot name CM31::inv alone (name_matcher: an inherent-impl path element matches only _, mod.rs PatElem::Impl vs ImplElem::Ty is 'TODO false'), so the pattern aspis_core::field::_::inv also covers M31::inv; elaboration of its body not checked"),
]
sha = lambda b: hashlib.sha256(b if isinstance(b, bytes) else b.encode()).hexdigest()
HDR = re.compile(r"/-- (?:Trait implementation: |Trait declaration: )?\[([^\]]*(?:\][^\]]*)*?)\](:? loop[^\n]*)?:?\n(?:\s+Source: '([^']*)', lines (\d+):\d+-(\d+):\d+)?")
DEF = re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(def|axiom|structure|inductive|instance|abbrev|opaque|impl_def)\b[ \t]*(\S*)')

def blocks(path):
    """doc blocks of a Lean file: rust name, loop flag, file, first and last source line, kind, Lean name, text"""
    p = Path(path)
    if not p.exists(): return []
    L = p.read_text().split('\n'); starts = [i for i, l in enumerate(L) if l.startswith('/-- ')]; out = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(L)
        while e > s + 1 and (L[e - 1].startswith('end ') or not L[e - 1].strip()): e -= 1
        b = '\n'.join(L[s:e]); m = HDR.match(b)
        if not m: continue
        body = re.sub(r'(?s)^/--.*?-/\n', '', b); kd = DEF.search(body)
        name = None
        if kd:
            name = kd.group(2)
            if not name:
                rest = body[kd.end():].split(); name = rest[0] if rest else None
        out.append(dict(rust=' '.join(m.group(1).split()), loop=bool(m.group(2)), file=m.group(3), beg=m.group(4), end=m.group(5),
                        kind=kd.group(1) if kd else None, lean=name, body=body, first=s + 1, last=e))
    return out

def item_extent(f, a, b):
    """the source lines of an item: the emission's doc-comment lines when they span more than one line; when they
    name one line only (Aeneas gives only the signature span for items of non-local crates), the item from that line to
    the closing brace of its body (or the terminating semicolon of a constant or static), found by brace matching
    after blanking comments, strings and character literals"""
    p = SRC / f
    if not f or not a or not p.exists(): return None, None
    a = int(a); b = int(b) if b else a
    if b > a: return a, b
    L = p.read_text().split('\n')
    depth = 0; seen = False
    for i in range(a - 1, len(L)):
        s = re.sub(r'//.*', '', L[i]); s = re.sub(r'"(?:\\.|[^"\\])*"', '""', s); s = re.sub(r"'(?:\\.|[^'\\])'", "''", s)
        for c in s:
            if c in '{([': depth += 1; seen = seen or c == '{'
            elif c in '})]': depth -= 1
            elif c == ';' and depth == 0: return a, i + 1
        if seen and depth == 0: return a, i + 1
    return a, a
def src_lines_sha(f, a, b):
    a, b = item_extent(f, a, b)
    if not a: return '', None
    L = (SRC / f).read_text().split('\n'); return sha('\n'.join(L[a - 1:b]) + '\n'), b
def why_not(e):
    if not e.startswith('no'): return ''
    if 'Application type mismatch' in e and ('U32' in e or 'expected to have type' in e): return 'does not elaborate: a shift amount of its own Rust type is passed to Std.<T>.wrapping_shl/shr, which the library defines for a U32 amount only (overflow checks off)'
    if 'ChunksExactMut' in e or 'Zip' in e: return 'does not elaborate: library item missing from the old library (Iterator instance of core::slice::ChunksExactMut and Zip over chunk iterators)'
    if 'expected a product type, got core.ops.control_flow.ControlFlow' in e: return 'does not elaborate: the ? on a Result returned with a back function by the opaque lifecycle_accounts is emitted as a triple destructuring of CoreOpsTry.branch, which the shim defines without back functions (library encoding)'
    return 'does not elaborate'

# ------------------------------------------------------------ normalisation for body comparison
def local_names(paths):
    names = set()
    for p in paths:
        for b in blocks(p):
            if b['lean']: names.add(b['lean'])
        if Path(p).exists():
            for m in re.finditer(r'(?m)^(?:structure|inductive|def|abbrev|axiom|opaque|impl_def)\s+([\w.«»\']+)', Path(p).read_text()): names.add(m.group(1))
    return names
def normaliser(ns, crate_prefix, names, modules=()):
    """rewrite a body of an emission whose local crate is `crate_prefix` (None for the program crate in X1) into
    crate-qualified names: `_root_.<ns>.x` and a dotted identifier whose first segment is a module of that crate and
    whose longest dotted prefix is a declaration of that emission get the crate prefix; the namespace is dropped"""
    tok = re.compile(r"(?<![\w.'«])(_root_\.%s\.)?([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)" % re.escape(ns))
    def fix(m):
        root, ident = m.group(1), m.group(2)
        if crate_prefix is None: return ident
        if root: return crate_prefix + '.' + ident
        parts = ident.split('.')
        if parts[0] not in modules: return ident
        for k in range(len(parts), 0, -1):
            if '.'.join(parts[:k]) in names: return crate_prefix + '.' + ident
        return ident
    def run(text):
        text = re.sub(r'(?s)^/--.*?-/\n', '', text)
        # Lean attributes are metadata (the whole-program run marks non-local items with rust_fun / rust_trait_impl
        # names that a per-crate run does not write); they are removed before the comparison
        text = re.sub(r'@\[(?:[^\]"]|"[^"]*")*\]\s*', '', text)
        text = tok.sub(fix, text).replace('_root_.' + ns + '.', '').replace(ns + '.', '')
        # AspisXPNewLib (used by the per-scope statement and core runs) holds the same five definitions as AspisTPNewLib
        text = text.replace('AspisXPNewLib.', 'AspisTPNewLib.')
        return '\n'.join(l.rstrip() for l in text.split('\n')).strip()
    return run
def ws(t): return ' '.join(t.split())

def diff_kind(a, b, la='X1', lb='other'):
    """a few words on how two normalised bodies differ"""
    ta, tb = ws(a), ws(b)
    if ta == tb: return 'whitespace / line breaks only'
    ka = collections.Counter(re.findall(r'\b(?:massert|fail|overflow|checked_\w+|wrapping_\w+|\+\.|-\.|\*\.)\b|[+\-*]\.?|\bI?U\d+\.(?:add|sub|mul)\w*', ta))
    kb = collections.Counter(re.findall(r'\b(?:massert|fail|overflow|checked_\w+|wrapping_\w+|\+\.|-\.|\*\.)\b|[+\-*]\.?|\bI?U\d+\.(?:add|sub|mul)\w*', tb))
    wa, wb = set(re.findall(r"[\w.']+", ta)), set(re.findall(r"[\w.']+", tb))
    only_a, only_b = sorted(wa - wb)[:6], sorted(wb - wa)[:6]
    full_a, full_b = wa - wb, wb - wa
    arith = any(re.search(r'wrapping|overflow|checked', x) for x in full_a | full_b)
    if not arith and all('.' not in x and not re.match(r'^\d', x) for x in full_a | full_b):
        cls = 'local bindings only (names or number of intermediate lets; the same called functions and constants); '
    elif not arith and all('.' not in x for x in full_a | full_b):
        cls = 'local bindings and literals; '
    elif not arith and full_b and all(re.match(r'^(\d+|usize|u8|u16|u32|u64|i32|Std\.\w+)$', x) for x in full_b if x not in full_a) and all(re.search(r'\.[A-Z0-9_]+$|^Result$|\.build_\w+$', x) for x in full_a):
        cls = 'constant: an initializer call on one side, its evaluated value on the other; '
    else: cls = ('arithmetic operators differ; ' if arith else 'called functions or constants differ; ')
    return cls + 'tokens only in %s: %s; only in %s: %s' % (la, ' '.join(only_a) or '-', lb, ' '.join(only_b) or '-')

def key(b): return (b['rust'], b['loop'], b['kind'] == 'axiom')

def main():
    RUN, OTHER, OUT = Path(sys.argv[1]), (None if sys.argv[2] == '-' else Path(sys.argv[2])), Path(sys.argv[3])
    OUT.mkdir(parents=True, exist_ok=True)
    cfg = json.loads((RUN / 'config.json').read_text()); res = json.loads((RUN / 'result.json').read_text())
    pre = cfg['prefix']; ns = cfg['ns']; setting = 'on' if cfg['overflow_checks'] else 'off'
    funs, ext = RUN / 'lean-src' / (pre + 'Funs.lean'), RUN / 'lean-src' / (pre + 'FunsExternal.lean')
    tyx = RUN / 'lean-src' / (pre + 'TypesExternal.lean')
    logp = RUN / 'summaries' / ('lean-%sFuns.log' % pre); lean = res.get('lean', {}).get('Funs', {})
    log = logp.read_text(errors='replace') if logp.exists() else None
    gaps = GAPS
    # function text against the pin
    fntext_p = OUT / 'fntext.json'
    if not fntext_p.exists():
        import subprocess
        files = sorted({str(p.relative_to(r)) for d in CRATE_DIR.values() for r in (SRC, PIN) if (r / d).exists() for p in (r / d).rglob('*.rs')})
        subprocess.run([sys.executable, '-I', str(W / 'frz-emit/bin/worker/TP_fntext.py'), 'dir:' + str(PIN), 'dir:' + str(SRC), str(fntext_p)] + files, stdout=open(OUT / 'fntext.txt', 'w'))
    fntext = json.loads(fntext_p.read_text())
    fb = blocks(funs); xb = blocks(ext)
    lean_of = {}
    for src, bl in (('Funs', fb), ('FunsExternal', xb)):
        for b in bl:
            if not b['loop'] and b['kind'] not in ('structure', 'inductive'): lean_of.setdefault((b['rust'], b['file'], b['beg']), (pre + src, ns + '.' + (b['lean'] or '?'), b['end']))
    # frza membership
    frza_rows = collections.defaultdict(set)
    for X, (crate, fns, st) in FRZA_SCOPES.items():
        for p in ('AspisFRZfrza%sFuns.lean' % X, 'AspisFRZfrza%sFunsExternal.lean' % X):
            for b in blocks(FRZA / 'lean-src' / p):
                if b['kind'] != 'axiom' and not b['loop']: frza_rows[b['rust']].add(X)
    rows = []
    for crate in CRATES:
        rr, other = F.make_rows(crate, funs, ext, log, lean.get('exit') if isinstance(lean, dict) else None, {}, gaps, False)
        for x in rr:   # rule 3 of the adapter rewrites module names in doc comments
            m = re.search(r'(?:^|/)_root_\.\w+\.(\w+)\.rs$', x['file'] or '')
            if m:
                c = [str(q.relative_to(SRC)) for q in (SRC / CRATE_DIR[crate]).rglob(m.group(1) + '.rs')]
                if len(c) == 1: x['file'] = c[0]
        have = {x['function'] for x in rr}
        for g in gaps:
            if g.get('row') and g['row'].split('::')[0] == crate and not any(re.search(g['match'], f) for f in have):
                rr.append(dict(function=g['row'], file=g['file'], line=g['line'], translates='not in this emission', elaborates='not run', gap=g['reason'], library=False))
        F.classify(rr, fntext, SRC, PIN, [])
        for x in rr:
            if x.get('translates') == 'not in this emission':
                g = next(g for g in gaps if g.get('row') == x['function'])
                x.update(crate=crate, lean_module='', lean_name='', end=g['end'], sha=src_lines_sha(x['file'], x['line'], g['end'])[0], frza=''.join(sorted(frza_rows.get(x['function'], ()))))
                continue
            mod, ln, end = lean_of.get((x['function'], x['file'] if '_root_' not in (x['file'] or '') else x['file'], x['line']), ('', '', None))
            if not mod:
                cand = [v for k, v in lean_of.items() if k[0] == x['function'] and k[2] == x['line']]
                mod, ln, end = cand[0] if cand else ('', '', None)
            h, end = src_lines_sha(x['file'], x['line'], end)
            x.update(crate=crate, lean_module=mod, lean_name=ln, end=end, sha=h, why=why_not(x['elaborates']), frza=''.join(sorted(frza_rows.get(x['function'], ()))))
        rows += rr
    cols = ('function', 'crate', 'file_line', 'source_revision', 'source_lines_sha256 (lines of file_line, newline-terminated)', 'translates', 'elaborates', 'lean_module', 'lean_name', 'overflow_checks', 'class_against_pin', 'pin_text', 'also_in_frza', 'note')
    with open(OUT / 'rows.tsv', 'w') as f:
        f.write('\t'.join(cols) + '\n')
        for x in rows:
            fl = '%s:%s-%s' % (x['file'], x['line'], x['end']) if x['file'] and x['line'] else (x['file'] or '')
            f.write('\t'.join(str(v).replace('\t', ' ') for v in (x['function'], x['crate'], fl, REV, x['sha'], x['translates'], x['elaborates'], x['lean_module'], x['lean_name'],
                                                                 setting, x['class'], x['pin'], x['frza'], x.get('gap') or x.get('why') or '')) + '\n')
    tot = collections.defaultdict(collections.Counter)
    for x in rows:
        c = F.category(x); tot[x['crate']][c] += 1; tot['all'][c] += 1; tot[x['crate']]['rows'] += 1; tot['all']['rows'] += 1
    # ---------------- externals
    def ext_class(r):
        top = r.split('::')[0]
        if top in ('core', 'alloc', 'std'): return 'std'
        if re.search(r'sol_log$|set_return_data$|Sysvar for solana_clock::Clock\}::get$|create_program_address$|create_with_seed$|hashv$', r): return 'Solana runtime (syscall on SBF; SDK host code in this build)'
        if top.startswith('solana_'): return 'SDK'
        if top in CRATES:
            for g in gaps:
                if re.search(g['match'], r): return 'named gap'
            return 'other (Aspis)'
        return 'other'
    exts = []
    for b in xb:
        if b['kind'] == 'axiom' and not b['loop']: exts.append(('function', b['rust'], b['file'] or '', b['beg'] or '', ns + '.' + (b['lean'] or '?')))
    for b in blocks(tyx):
        if b['kind'] in ('axiom', 'opaque', 'structure', 'inductive', 'def', 'abbrev'): exts.append(('type', b['rust'], b['file'] or '', b['beg'] or '', ns + '.' + (b['lean'] or '?')))
    with open(OUT / 'externals.tsv', 'w') as f:
        f.write('kind\trust_item\tsource\tlean_name\tclass\ttool_message\n')
        for k, r, fl, ln, lnm in exts:
            c = ext_class(r); msg = ''
            if c == 'named gap': msg = next(g['reason'] for g in gaps if re.search(g['match'], r))
            f.write('\t'.join((k, r, '%s:%s' % (fl, ln) if fl else '', lnm, c, msg)) + '\n')
    ext_tot = collections.Counter((k, ext_class(r)) for k, r, *_ in exts)
    # ---------------- completeness per crate against the LLBC
    doc = json.loads((RUN / 'runs' / 'C' / 'out.llbc').read_text()); tr = doc.get('translated', doc)
    files = {}
    for i, fl in enumerate(tr['files']):
        if not fl: continue
        n = fl['name'] if isinstance(fl, dict) else fl
        if isinstance(n, dict): n = list(n.values())[0]
        files[fl.get('id', i) if isinstance(fl, dict) else i] = str(n)
    def nm(f):
        o = []
        for x in f['item_meta']['name']: o.append(x['Ident'][0] if 'Ident' in x else '{impl}' if 'Impl' in x else '{%s}' % next(iter(x)))
        return '::'.join(o)
    ordered = set()
    for g in tr.get('ordered_decls') or []:
        for kind, v in g.items():
            if kind == 'Fun':
                for _, ids in v.items(): ordered.update(ids if isinstance(ids, list) else [ids])
    # spans from the RAW emission (the adaptation's compact/weights rules also rewrite module names inside doc-comment
    # Source paths; they touch no code: every `_root_.` occurrence in the adapted Funs is on a Source line)
    rawd = RUN / 'runs' / ('A-' + res.get('emission_used', 'release')) / 'raw' / ns
    leantext = (rawd / 'Funs.lean').read_text() if (rawd / 'Funs.lean').exists() else ''
    emitted = collections.Counter((fl, l) for fl, l in re.findall(r"Source: '([^']+)', lines (\d+):\d+-", leantext))
    emitted.update((fl, l) for fl, l in re.findall(r"macro invocation at: '([^']+)', lines (\d+):\d+-", leantext))
    axioms = collections.Counter((fl, l) for fl, l in re.findall(r"Source: '([^']+)', lines (\d+):\d+-", (rawd / 'FunsExternal_Template.lean').read_text() if (rawd / 'FunsExternal_Template.lean').exists() else ''))
    fix_root = lambda p: p if '_root_' not in p else p
    ne = []; per = collections.defaultdict(collections.Counter)
    opaque_by_flag = [re.sub(r'^crate::', 'aspis_r1_cost_probe_program::', o) for o in cfg.get('opaque', [])]
    for f in tr['fun_decls']:
        if not f: continue
        n = nm(f); crate = n.split('::')[0]
        if crate not in CRATES: continue
        body = f.get('body'); bk = next(iter(body)) if isinstance(body, dict) else body
        sp = f['item_meta']['span']; sp = sp.get('Untagged', sp); sp = sp.get('data', sp)
        fl = files.get(sp['file_id'], '?'); ln = str(sp['beg']['line'])
        fl = re.sub(r'^.*/src-frz-a/', '', fl)
        per[crate]['declarations'] += 1
        if bk != 'Structured':
            per[crate]['without a body in the LLBC (%s)' % bk] += 1
            if bk == 'Opaque': ne.append((crate, n, '%s:%s' % (fl, ln), 'opaque by flag (no body in the LLBC)', ''))
            continue
        per[crate]['with a body'] += 1
        if re.search(r'::\{impl\}::call_(once|mut)$', n) or emitted.get((fl, ln)):
            per[crate]['emitted with a definition'] += 1; continue
        if axioms.get((fl, ln)):
            per[crate]['emitted as an axiom'] += 1; ne.append((crate, n, '%s:%s' % (fl, ln), 'axiom in FunsExternal although Charon has a body', '')); continue
        fid = f.get('def_id')
        if fid not in ordered: why = 'unreachable from the root after Charon passes (not in ordered_decls); not referenced by any emitted definition'
        else: why = 'in ordered_decls but not emitted: dropped by Aeneas (non-local and unreferenced, PrePasses.simplify_trait_calls keep_group)'
        kind = 'drop glue' if n.endswith('{Builtin}') else 'derived Clone' if n.endswith('::clone') else 'derived PartialEq' if n.endswith('::eq') else 'derived Debug' if n.endswith('::fmt') else 'other'
        per[crate]['not emitted: ' + kind + (' (Charon-unreachable)' if fid not in ordered else ' (Aeneas-dropped)')] += 1
        ne.append((crate, n, '%s:%s' % (fl, ln), why, kind))
    # an emitted definition that calls an Aspis function with no definition and no axiom would show as an unknown
    # identifier in Lean; count those errors here
    unknown_aspis = re.findall(r'(?i)unknown (?:identifier|constant) [\'`]?([^\s\'`]+)', log or '')
    with open(OUT / 'not-emitted.tsv', 'w') as f:
        f.write('crate\tfunction (Charon name)\tsource\treason\tkind\n')
        for r in ne: f.write('\t'.join(r) + '\n')
    # ---------------- comparisons
    def bodies(run):
        c = json.loads((run / 'config.json').read_text()); p = c['prefix']
        return {key(b): b['body'] for b in blocks(run / 'lean-src' / (p + 'Funs.lean'))}, c
    def cmp_rows(a_bodies, a_norm, b_bodies, b_norm, restrict=None, la='a', lb='b'):
        out = []
        for k, ta in a_bodies.items():
            if restrict and not restrict(k): continue
            if k in b_bodies:
                na, nb = a_norm(ta), b_norm(b_bodies[k])
                st = 'identical' if na == nb else ('identical up to whitespace' if ws(na) == ws(nb) else 'different')
                out.append((k, st, '' if st.startswith('identical') else diff_kind(na, nb, la, lb)))
        return out
    x1 = {setting: bodies(RUN)}
    if OTHER: x1[json.loads((OTHER / 'config.json').read_text())['overflow_checks'] and 'on' or 'off'] = bodies(OTHER)
    x1norm = normaliser(ns, None, set())
    comp = []
    for X, (crate, fns, st) in FRZA_SCOPES.items():
        if st not in x1: comp.append((X, None, 'X1 run at overflow %s not available' % st, '')); continue
        xb_, _ = x1[st]
        fpre = 'AspisFRZfrza' + X
        fz = {key(b): b['body'] for b in blocks(FRZA / 'lean-src' / (fpre + 'Funs.lean'))}
        names = local_names([FRZA / 'lean-src' / (fpre + m + '.lean') for m in ('Types', 'Funs', 'TypesExternal', 'FunsExternal')])
        mods = {b['rust'].split('::')[1] for b in blocks(FRZA / 'lean-src' / (fpre + 'Funs.lean')) + blocks(FRZA / 'lean-src' / (fpre + 'Types.lean'))
                if b['rust'].startswith(crate + '::') and len(b['rust'].split('::')) >= 2}
        fnorm = normaliser(fns, None if crate == 'aspis_r1_cost_probe_program' else crate, names, mods)
        for k, s, d in cmp_rows(fz, fnorm, xb_, x1norm, la='frza', lb='X1'):
            comp.append((X, k, s, d))
    with open(OUT / 'compare-frza.tsv', 'w') as f:
        f.write('frza_scope\tfrza_overflow\tfunction\tloop_body\tresult\tdifference\n')
        for X, k, s, d in comp:
            if k is None: f.write('%s\t%s\t\t\t%s\t\n' % (X, FRZA_SCOPES[X][2], s)); continue
            f.write('\t'.join((X, FRZA_SCOPES[X][2], k[0], 'loop' if k[1] else '', s, d)) + '\n')
    comp_tot = collections.Counter((X, s) for X, k, s, d in comp if k)
    od = []
    if len(x1) == 2:
        (aon, _), (aoff, _) = x1['on'], x1['off']
        for k, s, d in cmp_rows(aoff, x1norm, aon, x1norm, la='off', lb='on'): od.append((k, s, d))
        only_off = [k for k in aoff if k not in aon]; only_on = [k for k in aon if k not in aoff]
        with open(OUT / 'overflow-diff.tsv', 'w') as f:
            f.write('function\tloop_body\tcrate\tresult\tdifference (off against on)\n')
            for k, s, d in od: f.write('\t'.join((k[0], 'loop' if k[1] else '', k[0].split('::')[0], s, d)) + '\n')
            for k in only_off: f.write('\t'.join((k[0], 'loop' if k[1] else '', k[0].split('::')[0], 'only in the off emission', '')) + '\n')
            for k in only_on: f.write('\t'.join((k[0], 'loop' if k[1] else '', k[0].split('::')[0], 'only in the on emission', '')) + '\n')
    od_tot = collections.Counter((k[0].split('::')[0], s) for k, s, d in od)
    summary = dict(run=str(RUN), setting=setting, totals={k: dict(v) for k, v in tot.items()}, externals={'%s / %s' % k: v for k, v in sorted(ext_tot.items())},
                   completeness={k: dict(v) for k, v in per.items()}, unknown_identifier_errors=unknown_aspis,
                   compare_frza={'%s %s' % k: v for k, v in sorted(comp_tot.items())}, overflow_diff={'%s %s' % k: v for k, v in sorted(od_tot.items())})
    json.dump(summary, open(OUT / 'summary.json', 'w'), indent=1)
    print(json.dumps(summary, indent=1))

if __name__ == '__main__': main()
