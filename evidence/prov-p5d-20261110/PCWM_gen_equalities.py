#!/usr/bin/env python3
"""PCWM_gen_equalities.py: emit PRVEq_<M>.lean, the per-definition equalities between a fresh frozen emission and the
committed gate module M (P0 prototype of the P2/P3 generator; see PCUH_HANDOFF.md).

Inputs
  --module M          gate module name, e.g. AspisR1WideToBytesSource.Funs or AdapterRwTypes
  --fresh-dir D       directory with the fresh Aeneas output (Funs.lean, Types.lean, *External_Template.lean)
  --fresh-ns NS       Aeneas namespace of the fresh emission (the -namespace argument)
  --gate-source F     committed source text of M (Funs or Types module); gives its namespace and declaration list
  --gate-types-source F   committed source of the sibling Types module (Funs modules only), for the identity check
  --partition P       PCUH_PARTITION.json (reached definitions of M are flagged; optional)
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
                                    else     a commented obligation (never unproved_placeholder or axiom) routed to P3
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
from PCWM_partition import uncomment

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
        # PCUE change 2 (P2a PARSE-1): a declaration placed directly after a `namespace`/`section`/`open`/... line (no blank line between)
        # is one raw block; peel those header lines so the declaration is recognised. The peeled lines are not part of the declaration text.
        while True:
            m0 = re.match(r'[ \t]*(?:namespace|section|open|set_option|variable|universe|noncomputable section)\b[^\n]*\n', rb)
            if not m0 or '\n' not in rb[m0.end():] and not rb[m0.end():].strip(): break
            start += m0.end(); rb = rb[m0.end():]
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
    # PCUH change 1 (= PCUC change 4): when `def` follows the attribute list on the SAME line, keep every column of that line
    eol = text.find('\n', k); same_line = text[k:(eol if eol >= 0 else len(text))].strip() != ''
    if same_line:
        span = k - i; new1 = ('@[' + ', '.join(kept) + ']') if kept else ''
        assert len(new1) <= span
        return text[:i] + new1.ljust(span) + text[k:]
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

def rename_fresh(a, text):
    """PCUH change 2 (= PCUB change 3): --rename-fresh OLD=NEW (repeatable). Rewrites the Lean path prefix OLD to NEW in the fresh text before it is parsed
    (word-boundary, path-prefix only); every rewrite is listed in the report."""
    for pr in (getattr(a, 'rename_fresh', None) or []):
        old, new = pr.split('=', 1)
        text = re.sub(r'(?<![\w.])' + re.escape(old) + r'(?=[\w.])' if old.endswith('.') else r'(?<![\w.])' + re.escape(old) + r'(?![\w.])', new, text)
    return text

def extract_namespace(text, ns):
    """PCUH change 5 (scope item 3, multi-namespace gate support): from a gate source with several top-level `namespace X ... end X` blocks (the same name may occur
    several times), keep the header (everything before the first namespace line) and the concatenated content of the blocks named `ns`; other namespaces are
    dropped from the block table (their constants still exist in the compiled gate module and resolve by name). Returns (new_text, other_namespaces)."""
    lines = text.split('\n'); head = []; segs = []; cur = None; others = []
    for l in lines:
        m = re.match(r'namespace\s+(\S+)\s*$', l)
        if m and cur is None:
            cur = m.group(1)
            if cur != ns and cur not in others: others.append(cur)
            if cur == ns: segs.append([])
            continue
        e = re.match(r'end\s+(\S+)\s*$', l)
        if e and cur is not None and e.group(1) == cur:
            cur = None; continue
        if cur is None:
            if not segs and not others: head.append(l)
        elif cur == ns: segs[-1].append(l)
    return '\n'.join(head) + '\nnamespace ' + ns + '\n' + '\n\n'.join('\n'.join(s) for s in segs) + '\nend ' + ns + '\n', others

def generate(a):
    M = a.module; TAG = getattr(a, 'tag', '') or ''; ML = M + TAG; fm = ML.replace('.', '_'); fresh_ns = 'PRVFresh_' + fm  # PCT patch 2: --tag for a second fresh dir
    gate_text = Path(a.gate_source).read_text(); gate_other_ns = []
    if getattr(a, 'gate_namespace', None): gate_text, gate_other_ns = extract_namespace(gate_text, a.gate_namespace)
    gh = header_info(gate_text)
    if getattr(a, 'gate_namespace', None): gh['namespaces'] = [a.gate_namespace]   # nested namespaces inside the selected block are part of its content
    assert len(gh['namespaces']) == 1, ('gate source must have one namespace', gh['namespaces'])
    gate_ns = gh['namespaces'][0]
    is_types = M.endswith('Types') or (Path(a.fresh_dir) / 'Funs.lean').exists() is False
    kind = 'types' if M.endswith('Types') else 'funs'
    if getattr(a, 'kind', None): kind = a.kind   # PCUE change 3: explicit kind for single-file gate modules
    NM = json.loads(Path(a.name_map).read_text()) if getattr(a, 'name_map', None) else {}   # PCUE change 4: fresh name -> gate name (recorded, deterministic)
    def gname(n): return NM.get(n, n)
    _keys = sorted(NM, key=len, reverse=True)
    _rx = re.compile(r"(?<![\w.'])(" + '|'.join(re.escape(k) for k in _keys) + r")(?![\w'])") if _keys else None
    def ren(t):   # apply the recorded name map textually (fresh name -> gate name); identity-modulo-map check only, emitted text is never rewritten
        return _rx.sub(lambda m: NM[m.group(1)], t) if _rx else t
    fresh_path = Path(a.fresh_dir) / ('Types.lean' if kind == 'types' else 'Funs.lean')
    fresh_text = rename_fresh(a, fresh_path.read_text()); fh = header_info(fresh_text)
    assert len(fh['namespaces']) == 1 and fh['namespaces'][0] == a.fresh_ns, ('fresh namespace', fh['namespaces'], a.fresh_ns)
    fblocks = [b for b in parse_blocks(fresh_text) if b['kind'] == 'decl']
    # PCUD patch 4: fully qualified references `_root_.<fresh ns>.x` count as references to the fresh declaration x (callee/closure detection only; emitted text unchanged)
    for b in fblocks: b['body'] = b['body'].replace('_root_.' + a.fresh_ns + '.', '')
    gblocks = {b['name']: b for b in parse_blocks(gate_text) if b['kind'] == 'decl'}
    # PCUH change 4: --gate-extra-source FILE (repeatable): declarations of gate modules IMPORTED by the gate module (same namespace) are added to the gate block table,
    # so that fresh callees defined there are compared with (and rewritten to) the compiled gate constants; the statements still name the compiled constants.
    for xs in (getattr(a, 'gate_extra_source', None) or []):
        for b in parse_blocks(Path(xs).read_text()):
            if b['kind'] == 'decl' and b['name'] not in gblocks: gblocks[b['name']] = b
    # ---- Types identity (Funs modules): fresh Types declarations vs committed Types declarations
    types_report = {}
    differing_types = set()
    ext_types = []; ext_funs = []
    if kind == 'funs':
        ftypes = {b['name']: b for b in parse_blocks(rename_fresh(a, (Path(a.fresh_dir) / 'Types.lean').read_text())) if b['kind'] == 'decl'}
        gtypes = {b['name']: b for b in parse_blocks(extract_namespace(Path(a.gate_types_source).read_text(), a.gate_namespace)[0] if getattr(a, 'gate_namespace', None) else Path(a.gate_types_source).read_text()) if b['kind'] == 'decl'}
        for n, b in ftypes.items():
            if gname(n) not in gtypes: types_report[n] = 'missing_in_gate'; differing_types.add(n)
            elif ren(norm_decl(b)) == norm_decl(gtypes[gname(n)]): types_report[n] = 'identical'
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
    INV = {v: k for k, v in NM.items()}
    reached = {INV.get(r, r) for r in reached}   # reached set expressed in fresh names
    LINE_MAP = []
    if getattr(a, 'bundle_offsets', None):
        LINE_MAP = json.loads(Path(a.bundle_offsets).read_text())['PRVEq_' + ML.replace('.', '_')]['line_map']
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
        common = [b for b in fblocks if gname(b['name']) in gate_names and b['dkind'] not in ('structure', 'inductive', 'axiom', 'opaque', 'class')]
    else:
        # Types module: only `def`/`abbrev` types whose body names no structure/inductive of the same file are equated by rfl;
        # simple parameterless structures get a generated Equiv; everything else is recorded as text-identical-only.
        common = []
        compound = {b['name'] for b in fblocks if b['dkind'] in ('structure', 'inductive')}
        for b in fblocks:
            n = b['name']
            if n in ext_set:
                type_info[n] = dict(cls='external_instantiated', gate_has_definition=n in gate_names, reached=False); continue
            if gname(n) not in gate_names:
                type_info[n] = dict(cls='missing_in_gate'); continue
            ident = ren(norm_decl(b)) == norm_decl(gblocks[gname(n)])
            toks = set(lean_ident_tokens(b['body'].split(':=', 1)[-1] if b['dkind'] in ('def', 'abbrev') else b['body']))
            if b['dkind'] in ('def', 'abbrev') and not (toks & compound):
                common.append(b); type_info[n] = dict(cls='rfl_candidate', identical=ident)
            elif b['dkind'] == 'structure':
                fl = parse_structure_fields(b['body'])
                def field_ok(t):
                    hit = set(lean_ident_tokens(t)) & ftype_names
                    if not hit: return True
                    # PCUH change 3 (= PCUB change 4): a field type mentioning only alias types already classed rfl_candidate is copied field-by-field; Lean checks the defeq
                    if all(type_info.get(h, {}).get('cls') == 'rfl_candidate' for h in hit): return True
                    return t.strip() in ftype_names and type_info.get(t.strip(), {}).get('cls') in ('rfl_candidate', 'equiv_candidate')
                ok = fl is not None and not b['name'].count(' ') and all(field_ok(t) for _, t in fl)
                type_info[n] = dict(cls='equiv_candidate' if ok else 'text_identical_only' if ident else 'differs', identical=ident, fields=fl if ok else None)
            elif b['dkind'] == 'inductive' and ident and parse_ctors(b['body'], n) is not None and not ((toks & compound) - {n}):
                # PCUI generic lemma class IND-EQUIV: an identical-text inductive whose constructor arguments mention no type declared in the same file
                type_info[n] = dict(cls='ind_equiv_candidate', identical=ident, ctors=parse_ctors(b['body'], n))
            else:
                type_info[n] = dict(cls='text_identical_only' if ident else 'differs', identical=ident)
    if getattr(a, 'only', None) and kind == 'funs':
        # PCUH change 1: compare only the scope definitions and their callee closure inside `common` (reached set of the partition is not used)
        onl = set(json.loads(Path(a.only).read_text())); cnames = [x['name'] for x in common]; cb = {x['name']: x for x in common}
        stack = [n for n in onl if n in cb]; keepc = set()
        while stack:
            n = stack.pop()
            if n in keepc: continue
            keepc.add(n); stack += [c for c in callees(cb[n]['body'], cnames, n) if c not in keepc]
        common = [x for x in common if x['name'] in keepc]
    plan = {}
    for b in common:
        n = b['name']
        cl = callees(b['body'], [x['name'] for x in common], n)
        mentions_diff_type = sorted(t for t in differing_types if t in set(lean_ident_tokens(b['body'])))
        plan[n] = dict(name=n, dkind=b['dkind'], reached=n in reached, callees=cl, mentions_differing_types=mentions_diff_type,
                       body_identical=(ren(norm_decl(b)) == norm_decl(gblocks[gname(n)])), status='pending', stage=None)
    equiv_order = []
    for b in fblocks:
        n = b['name']
        if kind == 'types' and type_info.get(n, {}).get('cls') == 'equiv_candidate':
            fl = type_info[n]['fields']
            deps = sorted({t.strip() for _, t in fl if t.strip() in type_info and type_info[t.strip()].get('cls') == 'equiv_candidate'})
            plan[n] = dict(name=n, dkind='structure-equiv', reached=n in reached, callees=deps, mentions_differing_types=[], body_identical=type_info[n]['identical'], status='pending', stage=None, fields=fl)
    for b in fblocks:
        n = b['name']
        if kind == 'types' and type_info.get(n, {}).get('cls') == 'ind_equiv_candidate':
            plan[n] = dict(name=n, dkind='inductive-equiv', reached=n in reached, callees=[], mentions_differing_types=[], body_identical=True, status='pending', stage=None, ctors=type_info[n]['ctors'])
    # PCUH change 2: --skip-divergent. Round-1 probes PCUH_L016/L017 (Native10/13 and Native14) hit the 180 s scope timeout with a stage-1 `rfl` between a fresh and a gate
    # loop whose bodies differ (non-identical `loop` fixpoints can make the defeq check diverge without charging heartbeats). A definition whose fresh and gate bodies are not token-equal
    # (after the recorded renames) and that mentions `loop`, and every definition that calls such a definition, is therefore NOT attempted: it becomes an obligation with the reason recorded.
    if getattr(a, 'skip_divergent', False) and kind == 'funs':
        div = set()
        for n, pl in plan.items():
            if pl['dkind'] in ('structure-equiv', 'inductive-equiv') or pl['body_identical']: continue
            fb_ = next(b for b in fblocks if b['name'] == n)
            if 'loop' in set(lean_ident_tokens(fb_['body'])) | set(lean_ident_tokens(gblocks[gname(n)]['body'])): div.add(n)
        ch = True
        while ch:
            ch = False
            for n, pl in plan.items():
                if n not in div and any(c in div for c in pl['callees']): div.add(n); ch = True
        for n in div:
            plan[n].update(status='failed', stage=None, error='NOT ATTEMPTED (PCUH change 2): fresh and gate bodies differ and the definition is, or calls, a loop whose defeq check diverged in the round-1 probe', preskipped=True)
    GIVEN = json.loads(Path(a.given).read_text()) if getattr(a, 'given', None) else {}
    for n_ in GIVEN:
        if n_ in plan: plan[n_].update(status='given', stage=None)
    # ---- ingest log
    if state and a.lean_log:
        for n, st in state['defs'].items():
            if n not in plan: continue
            lines = st.get('lines')
            if not lines or plan[n]['status'] == 'given': continue
            s, e = lines
            errs = [(l, m) for l in range(s, e + 1) for (k, m) in log_by_pos.get(l, []) if k == 'error']
            marks = stage_marks.get(f'PRVEq.{ML}.{n}', set()) | stage_marks.get(f'PRVEq.{ML}.{n}.equiv', set())
            stage = max(marks) if marks else None
            if errs or stage is None: plan[n].update(status='failed', stage=None, error=(errs[0][1][:300] if errs else 'no stage marker (not elaborated)'))
            else: plan[n].update(status='proved', stage=stage)
        # a stage-2 proof is accepted only if every callee equality it may have used is itself accepted
        for n in list(plan):
            p = plan[n]
            if p['status'] == 'proved' and p['stage'] == 2:
                bad = [c for c in p['callees'] if plan[c]['status'] not in ('proved', 'given')]
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
    # PCUD patch 3: --prune-fresh omits fresh declarations that are not in the callee closure of a compared (common) declaration.
    # Each equality unfolds only its own fresh closure, so omitted declarations cannot change any stated equality; the closure keeps every
    # callee/type name, so no omitted name can leak to a gate constant of the same name through `open`.
    keep = None
    if getattr(a, 'prune_fresh', False):
        fb_by = {b['name']: b for b in fblocks}; keep = set(); stack = [n for n in plan if n in fb_by]
        while stack:
            n = stack.pop()
            if n in keep: continue
            keep.add(n); stack += [c for c in callees(fb_by[n]['body'], fnames, n) if c not in keep]
    probe = not (state and a.lean_log and all(p['status'] in ('proved', 'failed') for p in plan.values()))
    # ---- emit
    out = []
    out.append(f'-- GENERATED by PCWM_gen_equalities.py for gate module {M}. Statements are against the gate constants of {M}.')
    out.append(f'-- fresh emission: {a.fresh_ns} -> {fresh_ns}; fresh source sha256 {sha(fresh_text)}')
    out.append('import Aeneas')
    out.append(f'import {M}')
    for xi in (getattr(a, 'extra_import', None) or []): out.append(f'import {xi}')
    out.append('open Aeneas Aeneas.Std Result ControlFlow Error')
    for so in fh['set_options']: out.append(so)
    if fh['noncomputable']: out.append('noncomputable section')
    out.append('')
    # PCUE change 1 (= PCWA change 1): fresh declarations live in a namespace NESTED INSIDE the gate namespace, so bare names resolve
    # through the enclosing namespace chain exactly as in the gate module (no `open` ambiguity with Aeneas.Std).
    if getattr(a, 'preamble', None): out.append(Path(a.preamble).read_text()); out.append('')
    out.append(f'namespace {gate_ns}')
    out.append(f'namespace {fresh_ns}')
    # PCT patch 1: also open the non-Aeneas namespaces the gate source opens (types supplied by a dependency module)
    for ol in gh['opens']:
        extra = [x for x in ol[5:].split() if x not in ('Aeneas', 'Aeneas.Std', 'Result', 'ControlFlow', 'Error', gate_ns)]
        if extra: out.append('open ' + ' '.join(extra))
    for ox in (getattr(a, 'open_extra', None) or []): out.append('open ' + ox)
    if getattr(a, 'fresh_prelude', None): out.append(Path(a.fresh_prelude).read_text()); out.append('')
    alias_types = []; open_prefix = []
    if kind == 'funs':
        ftn = set(ftypes)
        used = set(t for b in fblocks for t in lean_ident_tokens(b['body']))
        for t in sorted(ftn):
            if t in NM and t not in gate_names and any(u == t or u.startswith(t + '.') for u in used):
                alias_types.append(t)
                if NM[t] == 'aspis_core.' + t:
                    # gate carries the dependency-crate prefix: `open <gate ns>.aspis_core` resolves the bare fresh name (constructors and patterns included)
                    if not open_prefix:
                        out.append(f'/- PRVE name-map (prefix aspis_core.): fresh bare names of the aspis-core crate resolve to the gate names under {gate_ns}.aspis_core -/')
                        out.append(f'open {gate_ns}.aspis_core'); open_prefix.append(1)
                    continue
                out.append(f'/- PRVE name-map alias (recorded in the report; the Types pass of the same emission checks the identity): fresh type {t} is the gate type {NM[t]} -/')
                out.append(f'abbrev {t} := {gate_ns}.{NM[t]}')
    out.append('')
    subs = [dict(kind='namespace', old=a.fresh_ns, new=fresh_ns), dict(kind='imports_dropped', old=fh['imports'], new=[f'import {M}']),
            dict(kind='attributes_stripped', old=sorted(REG_ATTR.pattern.split('|')), new=[]), dict(kind='opened_namespace', old=None, new=gate_ns)]
    subs += [dict(kind='rename_fresh', old=x.split('=', 1)[0], new=x.split('=', 1)[1]) for x in (getattr(a, 'rename_fresh', None) or [])]
    fresh_lines = {}
    for b in fblocks:
        t = strip_reg_attrs(b['text'])
        t = re.sub(r'\b' + re.escape(a.fresh_ns) + r'\.', fresh_ns + '.', t)
        if kind == 'types' and b['name'] in ext_set: continue
        if keep is not None and b['name'] not in keep: continue
        if b['name'] in dropped:
            out.append('/- PRV-FRESH-DROPPED (did not elaborate against the gate environment, or depends on a dropped declaration):'); out.append(t); out.append('-/'); out.append('')
            continue
        s_line = len('\n'.join(out).split('\n')) + 1
        out.append(t)
        fresh_lines[b['name']] = [s_line, len('\n'.join(out).split('\n'))]
        out.append('')
    out.append(f'end {fresh_ns}')
    out.append(f'end {gate_ns}')
    out.append('')
    fresh_q = f'{gate_ns}.{fresh_ns}'
    # ---- equalities
    defs_state = {}
    def eqname(n): return f'PRVEq.{ML}.{n}'
    commented = []
    order = [b for b in fblocks if b['name'] in plan]
    for b in order:
        n = b['name']; p = plan[n]
        stmt = f'@{fresh_q}.{n} = @{gate_ns}.{gname(n)}'
        if p['status'] == 'given':
            out.append(GIVEN[n]); out.append(''); defs_state[n] = dict(lines=None); continue
        if p['dkind'] == 'inductive-equiv':
            emit_ind_equiv(out, defs_state, commented, p, n, fresh_q, gate_ns, eqname, M, gname)
            continue
        if p['dkind'] == 'structure-equiv':
            emit_equiv(out, defs_state, commented, p, n, fresh_q, gate_ns, eqname, M, gname)
            continue
        start_line = len('\n'.join(out).split('\n')) + 1
        if p['status'] == 'failed':
            reason = p.get('error', 'unproved')
            cls = classify_failure(p, b, gblocks[gname(n)])
            if p.get('blocked_by'): cls = plan[p['blocked_by'][0]].get('class', cls)
            out.append(f'/- PRV-OBLIGATION ({cls}; P3): {eqname(n)} : {stmt}')
            out.append(f'   last probe error: {reason[:200]!r} -/')
            out.append('')
            p['class'] = cls
            commented.append(n); defs_state[n] = dict(lines=None); continue
        cal = [eqname(c) for c in p['callees'] if plan[c]['status'] != 'failed']
        s1 = f'(trace "PRV-S1 {eqname(n)}"; rfl)'
        s2 = f'(trace "PRV-S2 {eqname(n)}"; delta {fresh_q}.{n} {gate_ns}.{gname(n)}; try simp only [{", ".join(cal)}]; try rfl; done)' if cal else f'(trace "PRV-S2 {eqname(n)}"; delta {fresh_q}.{n} {gate_ns}.{gname(n)}; try rfl; done)'
        if p['status'] == 'proved': tac = s1 if p['stage'] == 1 else s2
        else: tac = f'first | {s1} | {s2}'
        out.append('set_option maxHeartbeats 200000 in')   # PCUE change 6: LOWERED per-equality budget (never raised): a slow defeq check fails fast and becomes a recorded obligation
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
        if p and p['status'] == 'proved': c = ('lean_equiv_proved' if p['dkind'] in ('structure-equiv', 'inductive-equiv') else 'lean_eq_proved') + f'_stage{p["stage"]}'
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
    summary = dict(module=M, kind=kind, fresh_pruned=(sorted(n for n in fnames if keep is not None and n not in keep) if keep is not None else None), types=types_summary, fresh_dropped=sorted(dropped), names_resolved_to_gate_funs=leaks, gate_namespace=gate_ns, fresh_namespace=fresh_ns, probe_round=probe,
                   counts=dict(common_declarations=len(plan), reached_in_common=sum(1 for p in plan.values() if p['reached']),
                               fresh_declarations=len(fnames), gate_declarations=len(gblocks),
                               proved_rfl=sum(1 for p in plan.values() if p['status'] == 'proved' and p['stage'] == 1),
                               proved_unfold=sum(1 for p in plan.values() if p['status'] == 'proved' and p['stage'] == 2),
                               failed=sum(1 for p in plan.values() if p['status'] == 'failed'), pending=sum(1 for p in plan.values() if p['status'] == 'pending')),
                   reached_not_in_fresh=sorted(r for r in reached if r not in set(fnames)), fresh_not_in_gate=sorted(n for n in fnames if n not in gate_names),
                   types_identity=dict(identical=sorted(k for k, v in types_report.items() if v == 'identical'), differs=sorted(k for k, v in types_report.items() if v != 'identical')),
                   external_types=ext_types, external_funs=ext_funs,
                   externals_note='External boundary names of the fresh emission resolve, by name, to the gate constants through open <gate namespace>; the compile is the check. Each such boundary is an assumption inherited from the gate module, not proved here.',
                   substitutions=subs, gate_other_namespaces=gate_other_ns, name_map=NM, alias_types=alias_types,
                   per_definition={n: {k: v for k, v in p.items()} for n, p in plan.items()})
    return '\n'.join(out) + '\n', new_state, summary

LEAN_KW = {'at', 'from', 'in', 'do', 'fun', 'end', 'if', 'then', 'else', 'let', 'match', 'with', 'by', 'show', 'have', 'where', 'open', 'namespace', 'section', 'theorem', 'def', 'instance', 'structure', 'class', 'inductive', 'abbrev', 'macro', 'syntax', 'import', 'deriving', 'universe', 'variable', 'mut', 'return', 'for', 'unless', 'try', 'catch', 'finally', 'exact', 'intro', 'rfl', 'simp', 'rw', 'case', 'next', 'calc', 'using', 'only', 'local', 'private', 'protected', 'partial', 'unsafe', 'extends', 'forall', 'exists', 'Type', 'Sort', 'Prop'}
def qf(f): return '\u00ab' + f + '\u00bb' if f in LEAN_KW else f   # PCUE change 5 (P2a STRUCT-1): keyword-safe field names

def split_top_arrows(t):
    parts = []; depth = 0; cur = ''
    i = 0
    while i < len(t):
        ch = t[i]
        if ch in '([{': depth += 1
        if ch in ')]}': depth -= 1
        if depth == 0 and t.startswith('\u2192', i): parts.append(cur.strip()); cur = ''; i += 1; continue
        if depth == 0 and t.startswith('->', i): parts.append(cur.strip()); cur = ''; i += 2; continue
        cur += ch; i += 1
    parts.append(cur.strip()); return parts

def parse_ctors(body, tname):
    """PCUI IND-EQUIV: constructors of a parameterless `inductive T where | C : A -> B -> T` (or `| C (a : A) (b : B) : T`) as [(name, arity)]; None for other shapes."""
    m = re.match(r'\s*inductive\s+(\S+)\s+where\s*\n(.*)$', body.strip(), re.S)
    if not m or m.group(1) != tname: return None
    ctors = []
    for line in m.group(2).split('\n'):
        if not line.strip(): continue
        lm = re.match(r'^\s*\|\s*([A-Za-z_][A-Za-z0-9_\']*)\s*(.*)$', line)
        if not lm: return None
        name, rest = lm.group(1), lm.group(2)
        binders = 0
        while rest.startswith('('):
            d = 0; k = 0
            for k, ch in enumerate(rest):
                if ch == '(': d += 1
                if ch == ')':
                    d -= 1
                    if d == 0: break
            grp = rest[1:k]; names = grp.split(':', 1)[0].split()
            binders += len(names); rest = rest[k + 1:].lstrip()
        if not rest.startswith(':'): return None
        arrows = split_top_arrows(rest[1:].strip())
        if arrows[-1] != tname: return None
        ctors.append((name, binders + len(arrows) - 1))
    return ctors or None

def emit_ind_equiv(out, defs_state, commented, p, n, fresh_ns, gate_ns, eqname, M, gname=lambda x: x):
    T = f'{fresh_ns}.{n} \u2243 {gate_ns}.{gname(n)}'
    if p['status'] == 'failed':
        out.append(f'/- PRV-OBLIGATION (transport-needed; P3): {eqname(n)}.equiv : {T}'); out.append(f'   last probe error: {p.get("error","")[:200]!r} -/'); out.append('')
        p['class'] = 'transport-needed'; commented.append(n); defs_state[n] = dict(lines=None); return
    def arm(src, dst):
        out_ = []
        for c, k in p['ctors']:
            xs = ' '.join(f'a{i}' for i in range(k))
            out_.append(f'    | {src}.{n}.{c} {xs} => {dst}.{gname(n)}.{c} {xs}'.replace('  =>', ' =>'))
        return out_
    s1 = f'(trace "PRV-S1 {eqname(n)}"; cases x <;> rfl)'; r1 = f'(trace "PRV-S1 {eqname(n)}"; cases y <;> rfl)'
    start = len('\n'.join(out).split('\n')) + 1
    out.append('set_option maxHeartbeats 200000 in')
    out.append(f'def {eqname(n)}.equiv : {T} where')
    out.append('  toFun x := match x with'); out += arm(fresh_ns, gate_ns)
    out.append('  invFun y := match y with'); out += [l.replace(f'{fresh_ns}.{n}.', '@@F').replace(f'{gate_ns}.{gname(n)}.', f'@@G') for l in []]
    # inverse arms swap source and target
    for c, k in p['ctors']:
        xs = ' '.join(f'a{i}' for i in range(k))
        out.append(f'    | {gate_ns}.{gname(n)}.{c} {xs} => {fresh_ns}.{n}.{c} {xs}'.replace('  =>', ' =>'))
    out.append('  left_inv x := by'); out.append(f'    {s1}')
    out.append('  right_inv y := by'); out.append(f'    {r1}')
    end = len('\n'.join(out).split('\n'))
    out.append(f'#print axioms {eqname(n)}.equiv'); out.append('')
    defs_state[n] = dict(lines=[start, end])

def emit_equiv(out, defs_state, commented, p, n, fresh_ns, gate_ns, eqname, M, gname=lambda x: x):
    T = f'{fresh_ns}.{n} \u2243 {gate_ns}.{gname(n)}'
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
        if t in eq_for: return f'({eq_for[t]}.symm {src}.{qf(fname)})' if inv else f'({eq_for[t]} {src}.{qf(fname)})'
        return f'{src}.{qf(fname)}'
    tof = ', '.join(f'{qf(f)} := {val(f, t, "x", False)}' for f, t in fl)
    inv = ', '.join(f'{qf(f)} := {val(f, t, "y", True)}' for f, t in fl)
    s1 = f'(trace "PRV-S1 {eqname(n)}"; cases x; rfl)'; s2 = f'(trace "PRV-S2 {eqname(n)}"; cases x; simp)'
    r1 = f'(trace "PRV-S1 {eqname(n)}"; cases y; rfl)'; r2 = f'(trace "PRV-S2 {eqname(n)}"; cases y; simp)'
    tl = ('first | ' + s1 + ' | ' + s2) if p['status'] == 'pending' else (s1 if p['stage'] == 1 else s2)
    tr = ('first | ' + r1 + ' | ' + r2) if p['status'] == 'pending' else (r1 if p['stage'] == 1 else r2)
    start = len('\n'.join(out).split('\n')) + 1
    out.append('set_option maxHeartbeats 200000 in')
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
    ap.add_argument('--gate-extra-source', action='append', help='PCUH change 4: gate source of an imported gate module in the same namespace'); ap.add_argument('--gate-namespace', help='PCUH change 5: select one top-level namespace of a multi-namespace gate source'); ap.add_argument('--rename-fresh', action='append', help='PCUH change 2 (= PCUB change 3): OLD=NEW path-prefix rewrite of the fresh text'); ap.add_argument('--kind', choices=['funs', 'types'], help='PCUE change 3: override the kind (single-file gate modules)')
    ap.add_argument('--skip-divergent', action='store_true', help='PCUH change 2')
    ap.add_argument('--only', help='PCUH change 1: JSON list of fresh names; funs passes compare only these and their callee closure')
    ap.add_argument('--name-map', help='PCUE change 4: JSON {fresh declaration name: gate declaration name}')
    ap.add_argument('--open-extra', action='append', default=[], help='P2a: extra namespace opened inside the fresh namespace (gate refers to carrier types through an imported Types namespace)')
    ap.add_argument('--tag', default='', help='PCT patch 2: suffix for a second fresh directory of the same gate module')
    ap.add_argument('--preamble', help='PCUH: Lean text inserted before the gate namespace (generic lemmas)'); ap.add_argument('--fresh-prelude', help='PCUH: Lean text inserted at the start of the fresh namespace (constant bindings, recorded)'); ap.add_argument('--given', help='PCUH: JSON {fresh name: Lean text} of equalities proved by a hand-written block (emitted verbatim, treated as proved for callees)')
    ap.add_argument('--extra-import', action='append', default=[], help='PCUH: extra compiled module imported by the generated file')
    ap.add_argument('--bundle-offsets', help='PCUH_bundle.py offsets json; the Lean log is then a bundle log')
    ap.add_argument('--prune-fresh', action='store_true', help='PCUD patch 3: omit fresh declarations outside the callee closure of the compared declarations')
    a = ap.parse_args()
    assert not (a.state and a.lean_log and a.state_out is None), 'pass --state-out so the previous state is never overwritten'
    lean, st, summ = generate(a)
    Path(a.out).write_text(lean); Path(a.report).write_text(json.dumps(summ, indent=1) + '\n')
    so = a.state_out or (a.state if not (a.state and Path(a.state).exists()) else None)
    if so: Path(so).write_text(json.dumps(st, indent=1) + '\n')
    print(json.dumps(summ['counts']))
if __name__ == '__main__': main()
