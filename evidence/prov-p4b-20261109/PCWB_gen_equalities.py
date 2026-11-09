#!/usr/bin/env python3
"""PCWB_gen_equalities.py: emit PRVEq_<M>.lean, the per-definition equalities between a fresh frozen emission and the
committed gate module M (P0 prototype of the P2/P3 generator; see PCWB_HANDOFF.md).

Inputs
  --module M          gate module name, e.g. AspisR1WideToBytesSource.Funs or AdapterRwTypes
  --fresh-dir D       directory with the fresh Aeneas output (Funs.lean, Types.lean, *External_Template.lean)
  --fresh-ns NS       Aeneas namespace of the fresh emission (the -namespace argument)
  --gate-source F     committed source text of M (Funs or Types module); gives its namespace and declaration list
  --gate-types-source F   committed source of the sibling Types module (Funs modules only), for the identity check
  --partition P       PCWB_PARTITION.json (reached definitions of M are flagged; optional)
  --out F --report R  generated Lean file and JSON report
  --state S --lean-log L   iterate: ingest the Lean log of the previous compile of the same file (see below)

What the generated file contains (the Lean statements are against the gate's compiled constants, never a source file)
  import Aeneas / import M          M's compiled gate module (and, transitively, its Types and externals)
  namespace PRVFresh_<M>            the fresh emission, renamed by the recorded substitution list (report.substitutions):
                                    namespace NS -> PRVFresh_<M>; all imports of NS.* dropped; Aeneas registration attributes
                                    (rust_*, import_union_discriminant) stripped because they are keyed by Rust path and
                                    would be registered twice. open <gate namespace> makes types and external boundaries
                                    resolve to the committed constants WHEN the fresh Types text is identical (checked);
                                    fresh-namespace names take priority over opened names in Lean name resolution.
  PRVEq.<M>.<f>                     theorem @PRVFresh_<M>.f = @<gate ns>.f for each common declaration, callee-first:
                                    stage 1  rfl
                                    stage 2  delta both sides, rewrite with the already stated callee equalities, rfl
                                    else     a commented obligation (never sorry or axiom) routed to P3
  Each theorem carries a trace marker so one probe compile reveals which stage closed it:
      first | (trace "PRV-S1"; rfl) | (trace "PRV-S2"; delta ..; try simp only [..]; try rfl; done)
  Iteration: compile the emitted file once (probe). Feed the Lean log back with --state/--lean-log: theorems whose position
  has no error are accepted at the reported stage; failed ones, and those whose stage-2 proof used a failed callee
  equality, are turned into commented obligations and the pinned (stage-specific) tactic replaces the `first` chain.
  The regenerated file is then compiled once more to verify it; it is final when that compile reports no error.
"""
import argparse, json, re, sys, hashlib
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from PCWB_partition import uncomment

KW = r'(?:def|abbrev|structure|inductive|impl_def|opaque|axiom|theorem|instance|class)'
REG_ATTR = re.compile(r'(?:discriminant|rust_type|rust_trait_impl|rust_trait|rust_fun|rust_loop_body|rust_loop|rust_const|import_union_discriminant)\b')

def sha(s): return hashlib.sha256(s.encode()).hexdigest()

def split_attr(clean):
    """Return (attr_list_text, rest) for the leading @[...] attribute blocks of cleaned decl text."""
    i = 0; attrs = []
    while True:
        m = re.match(r'\s*@\[', clean[i:])
        if not m: break
        j = i + m.end(); depth = 1; k = j
        while k < len(clean) and depth:
            if clean[k] == '[': depth += 1
            elif clean[k] == ']': depth -= 1
            k += 1
        attrs.append(clean[j:k - 1]); i = k
    return attrs, clean[i:]

def parse_blocks(text):
    """Split an Aeneas-generated file into header lines and declaration blocks (callee-first file order)."""
    clean = uncomment(text)
    raw_blocks = re.split(r'\n[ \t]*\n', text)
    pos = 0; blocks = []
    for rb in raw_blocks:
        start = text.find(rb, pos); end = start + len(rb); pos = end
        cb = clean[start:end]
        attrs, rest = split_attr(cb)
        m = re.match(r'\s*((?:noncomputable|private|protected|partial|unsafe|nonrec)\s+)*(' + KW + r')\s+(?:\([^)]*\)\s*)?([^\s({:\[]+)', rest)
        if m and re.match(r'\s*(?:/--|@\[|(?:noncomputable|private|protected|partial|unsafe|nonrec|' + KW[3:-1] + r')\b)', rb) or (m and rb.lstrip().startswith(('/--', '@['))):
            blocks.append(dict(kind='decl', text=rb, attrs=attrs, dkind=m.group(2), name=m.group(3), body=rest))
        else:
            blocks.append(dict(kind='other', text=rb))
    return blocks

def header_info(text):
    """set_option lines, noncomputable section flag, namespace, imports."""
    clean = uncomment(text)
    ns = re.findall(r'(?m)^namespace\s+(\S+)', clean)
    return dict(namespaces=ns, imports=re.findall(r'(?m)^import\s+(\S+)', clean),
                set_options=[l.strip() for l in clean.splitlines() if l.startswith('set_option')],
                noncomputable=bool(re.search(r'(?m)^noncomputable section', clean)),
                opens=[l.strip() for l in clean.splitlines() if l.startswith('open ')])

def norm_decl(b):
    """Normalized declaration text for identity comparison: comments dropped, whitespace collapsed,
    Aeneas registration attributes dropped (they are metadata keyed by Rust path), other attributes kept."""
    attrs, rest = split_attr(uncomment(b['text']))
    keep = []
    for a in attrs:
        parts = [p.strip() for p in re.split(r',(?![^"]*"[^"]*(?:"[^"]*"[^"]*)*$)', a)]
        parts = [p for p in re.split(r',\s*(?=[A-Za-z_])', a) if p.strip()]
        kept = [p.strip() for p in parts if not REG_ATTR.match(p.strip())]
        if kept: keep.append(' '.join(', '.join(kept).split()))
    return ' '.join(('@[' + ', '.join(keep) + '] ' if keep else '') .split()) + ' ' + ' '.join(rest.split())

def strip_reg_attrs(text):
    """Remove Aeneas registration attributes from the attribute list(s) of a declaration block (text keeps doc comment)."""
    m = re.search(r'(?m)^@\[', text)
    if not m: return text
    i = m.start(); j = m.end(); depth = 1; k = j
    while k < len(text) and depth:
        if text[k] == '[': depth += 1
        elif text[k] == ']': depth -= 1
        k += 1
    inner = text[j:k - 1]
    # split on commas at top level, quote-aware
    parts = []; cur = ''; q = False; d = 0
    for ch in inner:
        if ch == '"': q = not q
        if not q and ch in '([': d += 1
        if not q and ch in ')]': d -= 1
        if ch == ',' and not q and d == 0: parts.append(cur); cur = ''
        else: cur += ch
    parts.append(cur)
    kept = [p.strip() for p in parts if p.strip() and not REG_ATTR.match(p.strip())]
    new = ('@[' + ', '.join(kept) + ']\n') if kept else ''
    rest = text[k:].lstrip('\n')
    return text[:i] + new + rest

def lean_ident_tokens(s):
    return re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", s)

def callees(body, names, self_name):
    toks = set(lean_ident_tokens(body))
    return [n for n in names if n != self_name and n in toks]


def parse_structure_fields(body):
    """Fields of a parameterless `structure T where` block: [(name, type_text)] or None if the shape is not simple."""
    m = re.match(r'structure\s+(\S+)\s+where\s*\n(.*)$', body.strip(), re.S)
    if not m: return None
    fields = []; cur = None
    for line in m.group(2).split('\n'):
        if not line.strip(): continue
        fm = re.match(r'^  ([A-Za-z_][A-Za-z0-9_\']*)\s*:(.*)$', line)
        if fm and not line.startswith('   '):
            cur = [fm.group(1), fm.group(2).strip()]; fields.append(cur)
        elif cur is not None and line.startswith('  '): cur[1] += ' ' + line.strip()
        else: return None
    return [(n, ' '.join(t.split())) for n, t in fields] if fields else None

def parse_externals(text):
    clean = uncomment(text)
    return sorted(set(m.group(1) for m in re.finditer(r'(?m)^\s*(?:@\[[^\]]*\]\s*)*axiom\s+(\S+)', clean)))

def generate(a):
    M = a.module; fm = M.replace('.', '_'); fresh_ns = 'PRVFresh_' + fm
    gate_text = Path(a.gate_source).read_text()
    gh = header_info(gate_text); assert len(gh['namespaces']) == 1, ('gate source must have one namespace', gh['namespaces'])
    gate_ns = gh['namespaces'][0]
    is_types = M.endswith('Types') or (Path(a.fresh_dir) / 'Funs.lean').exists() is False
    kind = 'types' if M.endswith('Types') else 'funs'
    fresh_path = Path(a.fresh_dir) / ('Types.lean' if kind == 'types' else 'Funs.lean')
    fresh_text = fresh_path.read_text(); fh = header_info(fresh_text)
    assert len(fh['namespaces']) == 1 and fh['namespaces'][0] == a.fresh_ns, ('fresh namespace', fh['namespaces'], a.fresh_ns)
    fblocks = [b for b in parse_blocks(fresh_text) if b['kind'] == 'decl']
    gblocks = {b['name']: b for b in parse_blocks(gate_text) if b['kind'] == 'decl'}
    # ---- Types identity (Funs modules): fresh Types declarations vs committed Types declarations
    types_report = {}
    differing_types = set()
    ext_types = []; ext_funs = []
    if kind == 'funs':
        ftypes = {b['name']: b for b in parse_blocks((Path(a.fresh_dir) / 'Types.lean').read_text()) if b['kind'] == 'decl'}
        gtypes = {b['name']: b for b in parse_blocks(Path(a.gate_types_source).read_text()) if b['kind'] == 'decl'}
        for n, b in ftypes.items():
            if n not in gtypes: types_report[n] = 'missing_in_gate'; differing_types.add(n)
            elif norm_decl(b) == norm_decl(gtypes[n]): types_report[n] = 'identical'
            else: types_report[n] = 'differs'; differing_types.add(n)
        ext_types = parse_externals((Path(a.fresh_dir) / 'TypesExternal_Template.lean').read_text()) if (Path(a.fresh_dir) / 'TypesExternal_Template.lean').exists() else []
        ext_funs = parse_externals((Path(a.fresh_dir) / 'FunsExternal_Template.lean').read_text()) if (Path(a.fresh_dir) / 'FunsExternal_Template.lean').exists() else []
    else:
        ext_types = parse_externals((Path(a.fresh_dir) / 'TypesExternal_Template.lean').read_text()) if (Path(a.fresh_dir) / 'TypesExternal_Template.lean').exists() else []
    # ---- reached definitions from the partition
    reached = set()
    if a.partition:
        P = json.loads(Path(a.partition).read_text()); mod = P['modules'].get(M)
        if mod:
            for n in mod['reached_definitions']:
                reached.add(n[len(gate_ns) + 1:] if n.startswith(gate_ns + '.') else n)
    LINE_MAP = []
    if getattr(a, 'bundle_offsets', None):
        LINE_MAP = json.loads(Path(a.bundle_offsets).read_text())['PRVEq_' + M.replace('.', '_')]['line_map']
    # ---- previous-round state
    state = json.loads(Path(a.state).read_text()) if a.state and Path(a.state).exists() else None
    log_by_pos = {}; stage_marks = {}
    if state and a.lean_log:
        for line in Path(a.lean_log).read_text().splitlines():
            mm = re.match(r'^PRV-S([12]) (\S+)', line)
            if mm: stage_marks.setdefault(mm.group(2), set()).add(int(mm.group(1)))
            m = re.match(r'^(?:\S*?)(?:PRVEq_[^:\s]+\.lean):(\d+):(\d+): (error|info|warning)\b[^:]*:?\s*(.*)$', line)
            if m:
                ln = int(m.group(1))
                if getattr(a, 'bundle_offsets', None):
                    inv = {b: j for j, b in LINE_MAP}
                    if ln not in inv: continue
                    ln = inv[ln]
                log_by_pos.setdefault(ln, []).append((m.group(3), m.group(4)))
    # ---- decide per-definition plan
    gate_names = set(gblocks)
    fnames = [b['name'] for b in fblocks]
    ext_set = set(ext_types) | set(ext_funs)
    ftype_names = set(fnames)
    type_info = {}
    if kind == 'funs':
        common = [b for b in fblocks if b['name'] in gate_names and b['dkind'] not in ('structure', 'inductive', 'axiom', 'opaque', 'class')]
    else:
        # Types module: only `def`/`abbrev` types whose body names no structure/inductive of the same file are equated by rfl;
        # simple parameterless structures get a generated Equiv; everything else is recorded as text-identical-only.
        common = []
        compound = {b['name'] for b in fblocks if b['dkind'] in ('structure', 'inductive')}
        for b in fblocks:
            n = b['name']
            if n in ext_set:
                type_info[n] = dict(cls='external_instantiated', gate_has_definition=n in gate_names, reached=False); continue
            if n not in gate_names:
                type_info[n] = dict(cls='missing_in_gate'); continue
            ident = norm_decl(b) == norm_decl(gblocks[n])
            toks = set(lean_ident_tokens(b['body'].split(':=', 1)[-1] if b['dkind'] in ('def', 'abbrev') else b['body']))
            if b['dkind'] in ('def', 'abbrev') and not (toks & compound):
                common.append(b); type_info[n] = dict(cls='rfl_candidate', identical=ident)
            elif b['dkind'] == 'structure':
                fl = parse_structure_fields(b['body'])
                def field_ok(t):
                    hit = set(lean_ident_tokens(t)) & ftype_names
                    if not hit: return True
                    return t.strip() in ftype_names and type_info.get(t.strip(), {}).get('cls') in ('rfl_candidate', 'equiv_candidate')
                ok = fl is not None and not b['name'].count(' ') and all(field_ok(t) for _, t in fl)
                type_info[n] = dict(cls='equiv_candidate' if ok else 'text_identical_only' if ident else 'differs', identical=ident, fields=fl if ok else None)
            else:
                type_info[n] = dict(cls='text_identical_only' if ident else 'differs', identical=ident)
    plan = {}
    for b in common:
        n = b['name']
        cl = callees(b['body'], [x['name'] for x in common], n)
        mentions_diff_type = sorted(t for t in differing_types if t in set(lean_ident_tokens(b['body'])))
        plan[n] = dict(name=n, dkind=b['dkind'], reached=n in reached, callees=cl, mentions_differing_types=mentions_diff_type,
                       body_identical=(norm_decl(b) == norm_decl(gblocks[n])), status='pending', stage=None)
    equiv_order = []
    for b in fblocks:
        n = b['name']
        if kind == 'types' and type_info.get(n, {}).get('cls') == 'equiv_candidate':
            fl = type_info[n]['fields']
            deps = sorted({t.strip() for _, t in fl if t.strip() in type_info and type_info[t.strip()].get('cls') == 'equiv_candidate'})
            plan[n] = dict(name=n, dkind='structure-equiv', reached=n in reached, callees=deps, mentions_differing_types=[], body_identical=type_info[n]['identical'], status='pending', stage=None, fields=fl)
    # ---- ingest log
    if state and a.lean_log:
        for n, st in state['defs'].items():
            if n not in plan: continue
            lines = st.get('lines')
            if not lines: continue
            s, e = lines
            errs = [(l, m) for l in range(s, e + 1) for (k, m) in log_by_pos.get(l, []) if k == 'error']
            marks = stage_marks.get(f'PRVEq.{M}.{n}', set()) | stage_marks.get(f'PRVEq.{M}.{n}.equiv', set())
            stage = max(marks) if marks else None
            if errs or stage is None: plan[n].update(status='failed', stage=None, error=(errs[0][1][:300] if errs else 'no stage marker (not elaborated)'))
            else: plan[n].update(status='proved', stage=stage)
        # a stage-2 proof is accepted only if every callee equality it may have used is itself accepted
        for n in list(plan):
            p = plan[n]
            if p['status'] == 'proved' and p['stage'] == 2:
                bad = [c for c in p['callees'] if plan[c]['status'] != 'proved']
                if bad: p.update(status='failed', stage=None, error='blocked by failed callee equalities: ' + ','.join(bad), blocked_by=bad)
        if state.get('final_pending'):
            pass
    # fresh-side errors: a fresh declaration that does not elaborate (e.g. an external boundary the gate models differently)
    # is dropped together with every fresh declaration that mentions it (a dropped name would otherwise leak to the gate
    # constant of the same name through `open`), and its equalities become obligations.
    dropped = set(state.get('dropped', [])) if state else set()
    if state and a.lean_log:
        for n, rng in state.get('fresh_lines', {}).items():
            s_, e_ = rng
            if any(k == 'error' for l in range(s_, e_ + 1) for (k, m) in log_by_pos.get(l, [])): dropped.add(n)
    changed = True
    while changed:
        changed = False
        for b in fblocks:
            if b['name'] not in dropped and any(c in dropped for c in callees(b['body'], fnames, b['name'])):
                dropped.add(b['name']); changed = True
    for n in dropped:
        if n in plan: plan[n].update(status='failed', stage=None, error='fresh declaration (or a callee) did not elaborate against the gate environment', fresh_dropped=True)
    probe = not (state and a.lean_log and all(p['status'] in ('proved', 'failed') for p in plan.values()))
    # ---- emit
    out = []
    out.append(f'-- GENERATED by PCWB_gen_equalities.py for gate module {M}. Statements are against the gate constants of {M}.')
    out.append(f'-- fresh emission: {a.fresh_ns} -> {fresh_ns}; fresh source sha256 {sha(fresh_text)}')
    out.append('import Aeneas')
    out.append(f'import {M}')
    out.append('open Aeneas Aeneas.Std Result ControlFlow Error')
    for so in fh['set_options']: out.append(so)
    if fh['noncomputable']: out.append('noncomputable section')
    out.append('')
    out.append(f'namespace {fresh_ns}')
    out.append(f'open {gate_ns}')
    out.append('')
    subs = [dict(kind='namespace', old=a.fresh_ns, new=fresh_ns), dict(kind='imports_dropped', old=fh['imports'], new=[f'import {M}']),
            dict(kind='attributes_stripped', old=sorted(REG_ATTR.pattern.split('|')), new=[]), dict(kind='opened_namespace', old=None, new=gate_ns)]
    fresh_lines = {}
    for b in fblocks:
        t = strip_reg_attrs(b['text'])
        t = re.sub(r'\b' + re.escape(a.fresh_ns) + r'\.', fresh_ns + '.', t)
        if kind == 'types' and b['name'] in ext_set: continue
        if b['name'] in dropped:
            out.append('/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):'); out.append(t); out.append('-/'); out.append('')
            continue
        s_line = len('\n'.join(out).split('\n')) + 1
        out.append(t)
        fresh_lines[b['name']] = [s_line, len('\n'.join(out).split('\n'))]
        out.append('')
    out.append(f'end {fresh_ns}')
    out.append('')
    # ---- equalities
    defs_state = {}
    def eqname(n): return f'PRVEq.{M}.{n}'
    commented = []
    order = [b for b in fblocks if b['name'] in plan]
    for b in order:
        n = b['name']; p = plan[n]
        stmt = f'@{fresh_ns}.{n} = @{gate_ns}.{n}'
        if p['dkind'] == 'structure-equiv':
            emit_equiv(out, defs_state, commented, p, n, fresh_ns, gate_ns, eqname, M)
            continue
        start_line = len('\n'.join(out).split('\n')) + 1
        if p['status'] == 'failed':
            reason = p.get('error', 'unproved')
            cls = classify_failure(p, b, gblocks[n])
            if p.get('blocked_by'): cls = plan[p['blocked_by'][0]].get('class', cls)
            out.append(f'/- PRV-OBLIGATION ({cls}; P3): {eqname(n)} : {stmt}')
            out.append(f'   last probe error: {reason[:200]!r} -/')
            out.append('')
            p['class'] = cls
            commented.append(n); defs_state[n] = dict(lines=None); continue
        cal = [eqname(c) for c in p['callees'] if plan[c]['status'] != 'failed']
        s1 = f'(trace "PRV-S1 {eqname(n)}"; rfl)'
        s2 = f'(trace "PRV-S2 {eqname(n)}"; delta {fresh_ns}.{n} {gate_ns}.{n}; try simp only [{", ".join(cal)}]; try rfl; done)' if cal else f'(trace "PRV-S2 {eqname(n)}"; delta {fresh_ns}.{n} {gate_ns}.{n}; try rfl; done)'
        if p['status'] == 'proved': tac = s1 if p['stage'] == 1 else s2
        else: tac = f'first | {s1} | {s2}'
        out.append(f'theorem {eqname(n)} : {stmt} := by')
        out.append(f'  {tac}')
        end_line = len('\n'.join(out).split('\n'))
        out.append(f'#print axioms {eqname(n)}')
        out.append('')
        defs_state[n] = dict(lines=[start_line, end_line])
    # types that exist in the gate but whose declaration texts we cannot equate in Lean here
    new_state = dict(module=M, kind=kind, fresh_lines=fresh_lines, dropped=sorted(dropped), defs={n: dict(defs_state.get(n, {}), **{k: v for k, v in plan[n].items() if k in ('status', 'stage', 'reached', 'callees', 'class', 'error')}) for n in plan},
                     probe=probe)
    types_summary = {}
    for n, ti in type_info.items():
        p = plan.get(n)
        if p and p['status'] == 'proved': c = ('lean_equiv_proved' if p['dkind'] == 'structure-equiv' else 'lean_eq_proved') + f'_stage{p["stage"]}'
        elif p and p['status'] == 'failed': c = 'lean_failed:' + p.get('class', '?')
        elif p: c = 'lean_pending'
        else: c = ti['cls']
        types_summary[n] = dict(status=c, reached=n in reached, text_identical=ti.get('identical'))
    if kind == 'types':
        for e in ext_types:
            types_summary[e] = dict(status='external_instantiated', reached=e in reached, text_identical=None, gate_defines=e in gate_names,
                                    note='fresh emission declares this type as an external axiom (TypesExternal_Template); the gate module supplies its definition: an inherited SDK/std model assumption, not proved here')
    fresh_names = set(fnames)
    tokens = set(t for b in fblocks for t in lean_ident_tokens(b['body']))
    leaks = sorted(t for t in tokens if t in gate_names and t not in fresh_names)
    summary = dict(module=M, kind=kind, types=types_summary, fresh_dropped=sorted(dropped), names_resolved_to_gate_funs=leaks, gate_namespace=gate_ns, fresh_namespace=fresh_ns, probe_round=probe,
                   counts=dict(common_declarations=len(plan), reached_in_common=sum(1 for p in plan.values() if p['reached']),
                               fresh_declarations=len(fnames), gate_declarations=len(gblocks),
                               proved_rfl=sum(1 for p in plan.values() if p['status'] == 'proved' and p['stage'] == 1),
                               proved_unfold=sum(1 for p in plan.values() if p['status'] == 'proved' and p['stage'] == 2),
                               failed=sum(1 for p in plan.values() if p['status'] == 'failed'), pending=sum(1 for p in plan.values() if p['status'] == 'pending')),
                   reached_not_in_fresh=sorted(r for r in reached if r not in set(fnames)), fresh_not_in_gate=sorted(n for n in fnames if n not in gate_names),
                   types_identity=dict(identical=sorted(k for k, v in types_report.items() if v == 'identical'), differs=sorted(k for k, v in types_report.items() if v != 'identical')),
                   external_types=ext_types, external_funs=ext_funs,
                   externals_note='External boundary names of the fresh emission resolve, by name, to the gate constants through open <gate namespace>; the compile is the check. Each such boundary is an assumption inherited from the gate module, not proved here.',
                   substitutions=subs,
                   per_definition={n: {k: v for k, v in p.items()} for n, p in plan.items()})
    return '\n'.join(out) + '\n', new_state, summary

def emit_equiv(out, defs_state, commented, p, n, fresh_ns, gate_ns, eqname, M):
    T = f'{fresh_ns}.{n} \u2243 {gate_ns}.{n}'
    if p['status'] == 'failed':
        out.append(f'/- PRV-OBLIGATION (transport-needed; P3): {eqname(n)}.equiv : {T}'); out.append(f'   last probe error: {p.get("error","")[:200]!r} -/'); out.append('')
        p['class'] = 'transport-needed'; commented.append(n); defs_state[n] = dict(lines=None); return
    def conv(t, x, direction):
        t = t.strip()
        if t in {c.split('.')[-1] for c in []}: pass
        return x
    fl = p['fields']; eq_for = {c: f'{eqname(c)}.equiv' for c in p['callees']}
    def val(fname, t, src, inv):
        t = t.strip()
        if t in eq_for: return f'({eq_for[t]}.symm {src}.{fname})' if inv else f'({eq_for[t]} {src}.{fname})'
        return f'{src}.{fname}'
    tof = ', '.join(f'{f} := {val(f, t, "x", False)}' for f, t in fl)
    inv = ', '.join(f'{f} := {val(f, t, "y", True)}' for f, t in fl)
    s1 = f'(trace "PRV-S1 {eqname(n)}"; cases x; rfl)'; s2 = f'(trace "PRV-S2 {eqname(n)}"; cases x; simp)'
    r1 = f'(trace "PRV-S1 {eqname(n)}"; cases y; rfl)'; r2 = f'(trace "PRV-S2 {eqname(n)}"; cases y; simp)'
    tl = ('first | ' + s1 + ' | ' + s2) if p['status'] == 'pending' else (s1 if p['stage'] == 1 else s2)
    tr = ('first | ' + r1 + ' | ' + r2) if p['status'] == 'pending' else (r1 if p['stage'] == 1 else r2)
    start = len('\n'.join(out).split('\n')) + 1
    out.append(f'def {eqname(n)}.equiv : {T} where')
    out.append(f'  toFun x := {{ {tof} }}')
    out.append(f'  invFun y := {{ {inv} }}')
    out.append(f'  left_inv x := by')
    out.append(f'    {tl}')
    out.append(f'  right_inv y := by')
    out.append(f'    {tr}')
    end = len('\n'.join(out).split('\n'))
    out.append(f'#print axioms {eqname(n)}.equiv'); out.append('')
    defs_state[n] = dict(lines=[start, end])

def classify_failure(p, fb, gb):
    if p.get('mentions_differing_types') or p.get('fresh_dropped'): return 'transport-needed'
    if p['body_identical']: return 'transport-needed'
    return 'semantic'

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--module', required=True); ap.add_argument('--fresh-dir', required=True); ap.add_argument('--fresh-ns', required=True)
    ap.add_argument('--gate-source', required=True); ap.add_argument('--gate-types-source'); ap.add_argument('--partition')
    ap.add_argument('--out', required=True); ap.add_argument('--report', required=True); ap.add_argument('--state'); ap.add_argument('--state-out'); ap.add_argument('--lean-log')
    ap.add_argument('--bundle-offsets', help='PCWB_bundle.py offsets json; the Lean log is then a bundle log')
    a = ap.parse_args()
    assert not (a.state and a.lean_log and a.state_out is None), 'pass --state-out so the previous state is never overwritten'
    lean, st, summ = generate(a)
    Path(a.out).write_text(lean); Path(a.report).write_text(json.dumps(summ, indent=1) + '\n')
    so = a.state_out or (a.state if not (a.state and Path(a.state).exists()) else None)
    if so: Path(so).write_text(json.dumps(st, indent=1) + '\n')
    print(json.dumps(summ['counts']))
if __name__ == '__main__': main()
