#!/usr/bin/env python3
"""X7 gates (iii') and (iv'): TYPE-BASED checks over an LLBC, replacing the callee-name gates of fv_x1b_mutiter.py and
fv_x1b_writecalls.py as the pass condition (the privacy lead's control crate, REVIEW.md section G of branch
codex/pv-aspis-rev2b-20261112, showed five shapes that this tool pair drops without an error and that both name scans
miss: `(&mut *a).into_iter().rev()`, `rev()` on an IterMut returned by a helper, iter_mut and rev split across two
functions, `RefCell::replace`, `Cell::set`). Bodies examined: every function of the LLBC with a body whose name starts
with the given prefix. Types are read from the LLBC (hash-consed values resolved; type names from `type_decls`).

mode iter, gate (iii'): FAIL for every `core::iter::adapters::rev::Rev<I>` instantiation anywhere in such a function
  (its signature, generics, locals, call generics, constants) where I is or contains a mutable iterator:
    - a type named IterMut, ChunksMut, ChunksExactMut, RChunksMut, RChunksExactMut, or array/vec IntoIter whose
      arguments hold `&mut`; or any `&mut` inside I;
    - a type variable of the function constrained by a trait clause that holds `&mut` (an iterator whose Item is
      `&mut T` / `&mut [T]`: the generic helper shape);
    - a type variable of the function that the function wraps in Rev without such a clause ("rev over parameter k"):
      then every call of that function, from any examined function, that instantiates position k with a mutable
      iterator (or with a type variable of the caller that is itself such a parameter, to a fixed point) FAILS at the
      caller (the split-across-two-functions shape).
  INFO (listed, not failing; the translator keeps these writes, section G shapes 2 and 3): every call of a
  `next_back` whose callee signature holds a mutable iterator type, and every call of an `rchunks*_mut`.
mode state, gate (iv'): FAIL for every call, from such a function that is not a named write boundary, of a
  `core::cell` method that stores or exposes a value for mutation, decided by the callee's name AND its signature
  type: Cell::{set, replace, swap, take, get_mut, as_ptr}, RefCell::{replace, replace_with, swap, take, get_mut,
  as_ptr, borrow_mut, try_borrow_mut}, RefMut::{deref_mut, index_mut}, UnsafeCell::{get, get_mut, raw_get}, and
  every `core::ptr` write (write, write_unaligned, write_volatile, write_bytes, copy, copy_nonoverlapping, swap,
  swap_nonoverlapping, replace, and the same methods of `*mut T`), and the SDK account handles try_borrow_mut_data /
  try_borrow_mut_lamports.
usage: fv_emit_gate_types.py iter|state <out.llbc> <prefix> [<boundary function last names, comma separated>]"""
import json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_x1b_llbc import LLBC, nm
from fv_emit_lean import rel

mode, path, pre = sys.argv[1], sys.argv[2], sys.argv[3]
bnd = set(x for x in (sys.argv[4] if len(sys.argv) > 4 else '').split(',') if x)
g = LLBC(path)
tn = {t['def_id']: nm(t['item_meta']['name']) for t in g.tr.get('type_decls', []) if t}
MUTN = re.compile(r'(^|::)(IterMut|ChunksMut|ChunksExactMut|RChunksMut|RChunksExactMut)$')


# Charon 454586e9 hash-conses each kind (types, spans, constants, clauses, layouts) in its own table, with
# overlapping ids; X1b's fv_x1b_llbc.py merges them into one table. Here a `Deduplicated` id is resolved by the
# context it occurs in: under a type position (`ty`, `types`, `inputs`, `output`, `Ref`, `RawPtr`, the element type
# of `Array`/`Slice`) through the TYPE table (payloads whose single key is a type constructor); under `span` not at
# all; elsewhere (calls only) through every non-type, non-span payload with that id (an over-approximation). The Rev
# search follows type positions only: every Rev value sits in a local, an argument, a return type or a generic.
TY_KEYS = {'Adt', 'TypeVar', 'Literal', 'Never', 'Ref', 'RawPtr', 'TraitType', 'DynTrait', 'FnPtr', 'FnDef', 'PtrMetadata', 'Array', 'Slice', 'Error'}
TY_CTX = {'ty', 'types', 'inputs', 'output', 'Ref', 'RawPtr', 'Slice', 'ty_'}
TY, OTHER = {}, {}
def _collect(x):
    stack = [x]
    while stack:
        v = stack.pop()
        if isinstance(v, dict):
            for k, w in v.items():
                if k in ('HashConsedValue', 'Value') and isinstance(w, list) and len(w) == 2 and isinstance(w[0], int):
                    pl = w[1]
                    if isinstance(pl, dict) and len(pl) == 1 and next(iter(pl)) in TY_KEYS: TY.setdefault(w[0], pl)
                    elif not (isinstance(pl, dict) and 'data' in pl and 'file_id' in pl.get('data', {})):
                        OTHER.setdefault(w[0], []).append(pl)
                stack.append(w)
        elif isinstance(v, list): stack.extend(v)
_collect(json.load(open(path)))


def walk(x, fn, ctx=None, other=True):
    """call fn on every dict node; `Deduplicated` resolved by context (see above)"""
    stack, vis = [(x, ctx)], set()
    while stack:
        v, c = stack.pop()
        if isinstance(v, list):
            stack.extend((w, c) for w in v); continue
        if not isinstance(v, dict): continue
        if len(v) == 1 and 'Deduplicated' in v and isinstance(v['Deduplicated'], int):
            i = v['Deduplicated']
            if c == 'span' or (i, c in TY_CTX) in vis: continue
            vis.add((i, c in TY_CTX))
            if c in TY_CTX:
                if i in TY: stack.append((TY[i], c))
            elif other:
                stack.extend((w, c) for w in OTHER.get(i, []))
            continue
        if len(v) == 1 and 'Value' in v and isinstance(v['Value'], list) and len(v['Value']) == 2 and isinstance(v['Value'][0], int):
            stack.append((v['Value'][1], c)); continue
        fn(v)
        for k, w in v.items():
            if k == 'Array' and isinstance(w, list) and len(w) == 2:
                stack.append((w[0], 'ty')); stack.append((w[1], 'const')); continue
            stack.append((w, k if k not in ('Untagged',) else c))


def facts(t):
    """(has a mutable iterator / &mut, set of free type variables) of a type tree"""
    st = {'mut': False, 'vars': set(), 'names': set()}
    def f(v):
        if 'Ref' in v and isinstance(v['Ref'], list) and len(v['Ref']) == 3 and v['Ref'][2] == 'Mut': st['mut'] = True
        if 'Adt' in v and isinstance(v['Adt'], dict):
            i = v['Adt'].get('id')
            i = i.get('Adt') if isinstance(i, dict) else i
            if isinstance(i, int):
                n = tn.get(i, ''); st['names'].add(n)
                if MUTN.search(n): st['mut'] = True
        if 'TypeVar' in v and isinstance(v['TypeVar'], dict):
            k = v['TypeVar'].get('Free', v['TypeVar'].get('Bound'))
            if isinstance(k, int): st['vars'].add(k)
            elif isinstance(k, list) and k and isinstance(k[-1], int): st['vars'].add(k[-1])
    walk(t, f)
    return st


def span_of(s):
    while isinstance(s, dict):
        if 'Untagged' in s: s = s['Untagged']; continue
        if 'Value' in s and isinstance(s['Value'], list): s = s['Value'][1]; continue
        if 'data' in s: s = s['data']; break
        return ('?', 0)   # a deduplicated span: its table is not resolved here; the caller's own first line is used
    return (rel(g.files.get(s.get('file_id'), '?')), (s.get('beg') or {}).get('line')) if isinstance(s, dict) and 'beg' in s else ('?', 0)


fsp = {i: span_of(f['item_meta']['span']) for i, f in g.fun.items()}
REV = [i for i, n in tn.items() if n == 'core::iter::adapters::rev::Rev']
examined = [i for i in g.direct if g.name[i].startswith(pre)]
fails, infos = set(), set()


def mutvars(f):
    """type variables of f constrained by a trait clause that holds &mut (Item = &mut ..)"""
    out = set()
    for cl in (f.get('generics') or {}).get('trait_clauses', []):
        fc = facts(cl)
        if fc['mut']: out |= fc['vars']
    fc = facts((f.get('generics') or {}).get('trait_type_constraints', []))
    if fc['mut']: out |= fc['vars']
    return out


if mode == 'iter':
    revpar = {}   # function id -> type-variable positions wrapped in Rev without a &mut clause
    for i in g.fun:
        f = g.fun[i]
        mv = mutvars(f)
        hits = []
        def onrev(v, hits=hits):
            if 'Adt' in v and isinstance(v['Adt'], dict):
                a = v['Adt'].get('id')
                a = a.get('Adt') if isinstance(a, dict) else a
                if a in REV:
                    hits.append(facts((v['Adt'].get('generics') or {}).get('types', [])))
        walk([f.get('signature'), f.get('body')], onrev, other=False)   # every value of a Rev type sits in a typed position
        for h in hits:
            if i in examined and (h['mut'] or (h['vars'] & mv)):
                why = 'Rev over ' + (', '.join(sorted(x for x in h['names'] if x)) or 'a type variable') + (' with &mut' if h['mut'] else ' (type variable whose trait clause holds &mut)')
                fails.add((g.name[i], fsp[i][0], fsp[i][1], 'Rev<I> instantiation', 'FAIL: ' + why))
            if h['vars']:
                revpar.setdefault(i, set()).update(h['vars'])
    # propagation: calls that instantiate a rev-wrapped parameter with a mutable iterator (fixed point over callers
    # that forward their own type variables)
    calls = {}
    for i in g.fun:
        f = g.fun[i]
        if not isinstance(f.get('body'), dict): continue
        lst = []
        def oncall(v, lst=lst):
            r = v.get('Regular') if isinstance(v.get('Regular'), dict) else None
            if r and isinstance(r.get('kind'), dict) and isinstance(r['kind'].get('Fun'), int):
                lst.append((r['kind']['Fun'], (r.get('generics') or {}).get('types', [])))
        walk(f['body'], oncall)
        calls[i] = lst
    changed = True
    while changed:
        changed = False
        for i, lst in calls.items():
            for c, tys in lst:
                for k in revpar.get(c, set()):
                    if k < len(tys):
                        fc = facts(tys[k])
                        if fc['mut'] and i in examined:
                            key = (g.name[i], fsp[i][0], fsp[i][1], 'call of %s' % g.name.get(c, '?'), 'FAIL: instantiates its Rev-wrapped type parameter %d with a mutable iterator (%s)' % (k, ', '.join(sorted(x for x in fc['names'] if x)) or '&mut'))
                            fails.add(key)
                        new = fc['vars'] - revpar.get(i, set())
                        if new:
                            revpar.setdefault(i, set()).update(new); changed = True
    # information: next_back on a mutable iterator, rchunks*_mut
    for i in examined:
        for c, tys in calls.get(i, []):
            cn = g.name.get(c, '')
            if cn.endswith('next_back') and facts(g.fun[c].get('signature'))['mut'] and any(MUTN.search(n) for n in facts(g.fun[c].get('signature'))['names']):
                infos.add((g.name[i], fsp[i][0], fsp[i][1], cn, 'INFO: next_back on a mutable iterator (write kept by this tool pair, section G shape 2)'))
            if re.search(r'rchunks(_exact)?_mut$', cn):
                infos.add((g.name[i], fsp[i][0], fsp[i][1], cn, 'INFO: rchunks_mut (write kept by this tool pair, section G shape 3)'))
else:
    CELLM = re.compile(r'^core::cell::.*::(set|replace|swap|take|get_mut|as_ptr|replace_with|borrow_mut|try_borrow_mut|deref_mut|index_mut|get|raw_get)$')
    PTR = re.compile(r'^core::ptr::(.*::)?(write|write_unaligned|write_volatile|write_bytes|copy|copy_nonoverlapping|swap|swap_nonoverlapping|replace)$')
    ACC = re.compile(r'try_borrow_mut_data$|try_borrow_mut_lamports$')
    for i in examined:
        lst = []
        def oncall(v, lst=lst):
            r = v.get('Regular') if isinstance(v.get('Regular'), dict) else None
            if r and isinstance(r.get('kind'), dict) and isinstance(r['kind'].get('Fun'), int): lst.append(r['kind']['Fun'])
        walk(g.fun[i]['body'], oncall)
        for c in set(lst):
            cn = g.name.get(c, '')
            hit = None
            if CELLM.search(cn):
                names = facts(g.fun[c].get('signature'))['names'] if c in g.fun else set()
                cells = sorted(n for n in names if re.search(r'core::cell::(Cell|RefCell|UnsafeCell|RefMut)$', n))
                meth = cn.split('::')[-1]
                if meth == 'get' and not any(n.endswith('UnsafeCell') for n in cells): cells = []   # Cell::get / RefCell::get are reads
                if cells: hit = 'core::cell method %s on %s' % (meth, '/'.join(c2.split('::')[-1] for c2 in cells))
            elif PTR.search(cn) or ACC.search(cn):
                hit = cn
            if hit:
                last = g.name[i].split('::')[-1]
                fails.add((g.name[i], fsp[i][0], fsp[i][1], cn, ('allowed: write boundary ' if last in bnd else 'FAIL: ') + hit))
    fails = {r for r in fails if r[4].startswith('FAIL')} | {r for r in fails if not r[4].startswith('FAIL')}
print('function\tfile\tline\tsite\tverdict')
nfail = 0
for r in sorted(fails | infos):
    print('\t'.join(map(str, r)))
    nfail += r[4].startswith('FAIL')
tag = "gate (iii') Rev over a mutable iterator, by type" if mode == 'iter' else "gate (iv') core::cell / ptr / account mutation calls, by type"
print('%s [%s, prefix %s]: %s (%d failing, %d information rows)' % (tag, path, pre, 'pass' if nfail == 0 else 'FAIL', nfail, len(infos)))
sys.exit(0 if nfail == 0 else 1)
