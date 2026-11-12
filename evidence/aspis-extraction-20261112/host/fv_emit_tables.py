#!/usr/bin/env python3
"""X7: the two tables of one program's emission. Reads only; writes <run>/<program>/rows.tsv and externals.tsv.

rows.tsv: one row per Aspis declaration of the raw emission: every block of Funs.lean whose source lies in one of
  the five Aspis crates (functions, their loop and loop-body definitions, closures, trait-impl structures, constants),
  plus every bodiless Aspis declaration of the templates. Columns: function (Rust path as Aeneas names it, with
  Aeneas's label such as `loop body 0`), crate, file:line (the item's source lines: X1's rule, fv_emit_lean.item_extent),
  sha256 of those source lines (joined with newlines, newline-terminated), translates (yes: a definition with a
  body; no: bodiless), elaborates (yes / no: the native compile reports an error in the declaration / unknown: the
  module did not finish), Lean name (with the namespace), Lean kind.
externals.tsv: every bodiless declaration (`axiom`/`opaque`) of the four raw files, classed write boundary, runtime
  wrapper (both named in the program config), std (core, alloc, std), Solana runtime (the SDK calls that are syscalls
  or runtime services on SBF: the regex of X2's fv_x2_externals.py), SDK (other solana_* items), other. For std,
  SDK and Solana runtime functions: the Aspis functions of the LLBC whose body calls it, each with the file and line
  of the calling statement (edge rule of X1b's fv_x1b_llbc.py / fv_x1b_callers.py; closures and loop bodies are listed
  under their own LLBC names; where the LLBC gives the statement no span, the calling function's first line).
usage: fv_emit_tables.py <program config.json> <tree> <run dir>"""
import hashlib, json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_emit_lean import blocks, crate_of, item_extent, rel
from fv_x1b_llbc import LLBC

cfg, tree, run = json.loads(Path(sys.argv[1]).read_text()), Path(sys.argv[2]), Path(sys.argv[3])
P = run / cfg['program']; ns = cfg['ns']; R = P / 'aeneas' / 'raw' / ns
sha = lambda s: hashlib.sha256(s.encode()).hexdigest()
# ---------------- native compile result
err_decls = set()
nat = P / 'native-errors.tsv'
if nat.exists():
    for l in nat.read_text().splitlines()[1:]:
        if l.startswith('#') or not l.strip(): continue
        f = l.split('\t'); err_decls.add((f[0], f[2]))
mod_ok = {}
ex = P / 'native' / 'exit.txt'
if ex.exists():
    for l in ex.read_text().splitlines():
        f = l.split()
        mod_ok[f[0]] = (f[1] == '0') or (int(f[3]) > 0)   # finished: exit 0, or exit 1 with errors reported
srclines = {}
def src_sha(f, a, b):
    a, b = item_extent(tree, f, a, b)
    if not a: return '', ''
    if f not in srclines: srclines[f] = (tree / f).read_text(errors='replace').split('\n')
    return '%s:%d-%d' % (f, a, b), sha('\n'.join(srclines[f][a - 1:b]) + '\n')
rows = []
for M, fn in (('Funs', 'Funs.lean'), ('FunsExternal', 'FunsExternal_Template.lean'), ('Types', 'Types.lean'), ('TypesExternal', 'TypesExternal_Template.lean')):
    for b in blocks(R / fn):
        c = crate_of(b['file'], b['rust'])
        if not c or not b['kind']: continue
        if M == 'Types' or (M == 'TypesExternal' and b['kind'] not in ('axiom', 'opaque')):
            continue
        bodiless = b['kind'] in ('axiom', 'opaque')
        loc, h = src_sha(rel(b['file']), b['a'], b['b'])
        if not mod_ok.get(M):
            el = 'unknown'
        else:
            el = 'no' if (M, b['lean']) in err_decls else 'yes'
        rows.append((b['rust'] + ((': ' + b['label']) if b['label'] else ''), c, loc, h,
                     'no: bodiless (opaque by name)' if bodiless else 'yes', el, ns + '.' + b['lean'], b['kind'] + ' (' + M + ')'))
with open(P / 'rows.tsv', 'w') as fo:
    fo.write('function\tcrate\tfile_lines\tsource_sha256\ttranslates\telaborates\tlean_name\tlean_kind\n')
    for r in rows: fo.write('\t'.join(r) + '\n')
# ---------------- externals
RUNTIME = re.compile(r'solana_(program|cpi)::program::(invoke|invoke_signed|invoke_unchecked|invoke_signed_unchecked|set_return_data|get_return_data)|'
                     r'solana_cpi::|::get_return_data|::set_return_data|solana_sysvar::|Sysvar|::get$|find_program_address|create_program_address|'
                     r'try_find_program_address|solana_msg::|sol_log|sol_memcmp|sol_memcpy|sol_memset|solana_program_memory::|get_stack_height|'
                     r'solana_sha256_hasher::hashv|solana_program::hash::hashv')
g = LLBC(str(P / 'charon' / 'out.llbc'))
def norm(rust):
    buf, depth = '', 0
    for ch in rust:
        if ch == '{':
            if depth == 0: buf += '{impl}'
            depth += 1
        elif ch == '}': depth -= 1
        elif depth == 0: buf += ch
    return re.sub(r'<[^<>]*>', '', buf)
def span_of(s):
    if not isinstance(s, dict): return None
    if 'Deduplicated' in s: s = g.HC.get(s['Deduplicated'], {})
    if isinstance(s, dict) and 'Value' in s: s = s['Value'][1]
    s = s.get('Untagged', s) if isinstance(s, dict) else s
    s = s.get('data', s) if isinstance(s, dict) else s
    return (rel(g.files.get(s.get('file_id'), '?')), s.get('beg', {}).get('line')) if isinstance(s, dict) and 'beg' in s else None
def calls(body, sp0=None):
    out = set(); stack = [(body, sp0)]; seen = set()
    while stack:
        v, sp = stack.pop()
        if isinstance(v, list): stack.extend((w, sp) for w in v); continue
        if not isinstance(v, dict): continue
        if 'span' in v and ('kind' in v or 'content' in v): sp = span_of(v['span']) or sp
        for k, w in v.items():
            if k == 'Drop': continue
            if k == 'Deduplicated' and isinstance(w, int):
                if (w, sp) not in seen: seen.add((w, sp)); stack.append((g.HC.get(w), sp))
                continue
            if k == 'Regular' and isinstance(w, dict) and isinstance(w.get('kind'), dict) and isinstance(w['kind'].get('Fun'), int):
                out.add((w['kind']['Fun'], sp))
            stack.append((w, sp))
    return out
by_span, by_name = {}, {}
for i, f in g.fun.items():
    s = span_of(f['item_meta']['span'])
    if s: by_span.setdefault(s, set()).add(i)
    by_name.setdefault(norm(g.name[i]), set()).add(i)
callers = {}
for i in g.direct:
    if not g.name[i].startswith('aspis_'): continue
    for c, sp in calls(g.fun[i]['body'], span_of(g.fun[i]['item_meta']['span'])):
        if c not in g.direct:
            callers.setdefault(c, set()).add((g.name[i], sp[0] if sp else '?', sp[1] if sp else 0))
wb, rw = set(cfg['write_boundaries']), set(cfg['runtime_wrappers'])
ext = []
for fn in ('FunsExternal_Template.lean', 'TypesExternal_Template.lean', 'Funs.lean', 'Types.lean'):
    for b in blocks(R / fn):
        if b['kind'] not in ('axiom', 'opaque'): continue
        rust, lean = b['rust'], b['lean']
        top = re.split(r'::|\{|<|\[|\s', rust.lstrip('{[<&\'0 '), 1)[0]
        if lean in wb: cls = 'write boundary'
        elif lean in rw: cls = 'runtime wrapper'
        elif crate_of(b['file'], rust): cls = 'other (Aspis)'
        elif top in ('core', 'alloc', 'std') or b['file'].startswith('/rustc/'): cls = 'std'
        elif RUNTIME.search(rust): cls = 'Solana runtime'
        elif top.startswith('solana'): cls = 'SDK'
        else: cls = 'other'
        is_type = 'Types' in fn
        cl = ''
        if not is_type and cls in ('std', 'SDK', 'Solana runtime'):
            ids = by_span.get((rel(b['file']), b['a']), set()) or by_name.get(norm(rust), set())
            cs = set()
            for i in ids: cs |= callers.get(i, set())
            cl = '; '.join('%s (%s:%s)' % x for x in sorted(cs)) if cs else ('no Aspis caller in the LLBC (called from std/SDK code or a trait instance)' if ids else 'not matched to an LLBC function')
        ext.append((rust, 'type' if is_type else 'function', ns + '.' + lean, cls, '%s:%s' % (b['file'], b['a']), fn, cl))
with open(P / 'externals.tsv', 'w') as fo:
    fo.write('rust_path\tkind\tlean_name\tclass\tsource\tlean_file\taspis_callers (file:line of the call)\n')
    for r in ext: fo.write('\t'.join(str(x).replace('\t', ' ') for x in r) + '\n')
cnt = {}
for r in ext: cnt[(r[3], r[1])] = cnt.get((r[3], r[1]), 0) + 1
print('%s: rows %d (bodiless Aspis %d; elaborates no %d, unknown %d); externals %d: %s' % (cfg['program'], len(rows), sum(1 for r in rows if r[4] != 'yes'),
      sum(1 for r in rows if r[5] == 'no'), sum(1 for r in rows if r[5] == 'unknown'), len(ext), ', '.join('%s %s %d' % (k[0], k[1], v) for k, v in sorted(cnt.items()))))
