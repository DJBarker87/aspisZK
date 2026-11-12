#!/usr/bin/env python3
"""X7 helper (imported by fv_emit_gate_writeroute.py and fv_emit_gate_targetos.py; reads only): which source lines a
build compiles, from the `#[cfg(...)]` attributes of the Rust sources and the resolved feature set of each crate.

- features(path): the feature sets of `cargo tree -e normal --prefix none -f '{p}|{f}'` output, per package name
  (union over repeated lines).
- parse(expr) / value(ast, feats, target): a `cfg` predicate over all/any/not, `feature = ".."`, `target_os = ".."`,
  `target_arch`, `target_family`, `test`, `debug_assertions`, `doc`, `miri`, `kani`, and custom flags (`aeneas_ref`, ..:
  false, since no build passes --cfg; recorded in CUSTOM_FLAGS). target is 'host' (Charon's
  x86_64-unknown-linux-gnu build) or 'sbf' (sbpf-solana-solana). A release build: test, debug_assertions, doc, miri
  and kani are false. Any other predicate is None (unknown); all/any/not propagate None.
- sites(text): every `#[cfg(..)]` attribute (not cfg_attr) with the extent of the item, statement or block it gates:
  from the first token after the attribute (and after any further attribute lines) to the `;` or `,` at depth 0, or to
  the brace that closes the first `{` opened at depth 0. Comments, strings and character literals are blanked first.
- inactive(text, feats, target): the line ranges (1-based, inclusive) a build drops: gated by a predicate that is
  false. An unknown predicate drops nothing (and is reported by the gate that uses it)."""
import re
from pathlib import Path


def features(path):
    out = {}
    p = Path(path)
    if not p.exists():
        return out
    for l in p.read_text(errors='replace').splitlines():
        if '|' not in l:
            continue
        pkg, f = l.split('|', 1)
        name = pkg.strip().split(' ')[0]
        out.setdefault(name, set()).update(x for x in f.strip().split(',') if x)
    return out


CUSTOM_FLAGS = set()
TOK = re.compile(r'\s*(?:([A-Za-z_][A-Za-z0-9_]*)|("(?:\\.|[^"\\])*")|([(),=]))')


def parse(expr):
    toks, pos = [], 0
    while pos < len(expr):
        m = TOK.match(expr, pos)
        if not m or m.end() == pos:
            if expr[pos:].strip() == '':
                break
            raise ValueError('cfg tokenize at %r' % expr[pos:])
        pos = m.end()
        toks.append(m.group(1) or m.group(2) or m.group(3))
    i = [0]

    def pred():
        name = toks[i[0]]; i[0] += 1
        if i[0] < len(toks) and toks[i[0]] == '=':
            i[0] += 1; v = toks[i[0]]; i[0] += 1
            return ('kv', name, v.strip('"'))
        if i[0] < len(toks) and toks[i[0]] == '(':
            i[0] += 1; args = []
            while toks[i[0]] != ')':
                args.append(pred())
                if toks[i[0]] == ',':
                    i[0] += 1
            i[0] += 1
            return (name, args)
        return ('flag', name)
    r = pred()
    return r


def value(ast, feats, target):
    k = ast[0]
    if k == 'kv':
        _, n, v = ast
        if n == 'feature':
            return v in feats
        if n == 'target_os':
            return v == ('solana' if target == 'sbf' else 'linux')
        if n == 'target_arch':
            return v in (('sbf', 'bpf') if target == 'sbf' else ('x86_64',))
        if n == 'target_family':
            return (v == 'unix') if target == 'host' else False
        return None
    if k == 'flag':
        if ast[1] in ('test', 'debug_assertions', 'doc', 'miri', 'kani'):
            return False
        if ast[1] in ('unix',):
            return target == 'host'
        # a custom cfg flag: the deployed builds and the Charon runs pass no --cfg (RUSTFLAGS hold only thread and
        # linker options), so it is unset; every such name is recorded and printed by the gates
        CUSTOM_FLAGS.add(ast[1])
        return False
    vals = [value(a, feats, target) for a in ast[1]]
    if k == 'all':
        return False if False in vals else (None if None in vals else True)
    if k == 'any':
        return True if True in vals else (None if None in vals else False)
    if k == 'not':
        return None if vals[0] is None else not vals[0]
    return None


def blank(text):
    """comments, strings and character literals replaced by spaces (newlines kept, so offsets and lines stay)"""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith('//', i):
            j = text.find('\n', i); j = n if j < 0 else j
            for k in range(i, j): out[k] = ' '
            i = j
        elif text.startswith('/*', i):
            j = text.find('*/', i + 2); j = n if j < 0 else j + 2
            for k in range(i, j):
                if out[k] != '\n': out[k] = ' '
            i = j
        elif c == '"' or (c == 'b' and text.startswith('b"', i)) or (c == 'r' and re.match(r'r#*"', text[i:i + 4])):
            m = re.match(r'b?r(#*)"', text[i:i + 6])
            if m:
                close = '"' + m.group(1); j = text.find(close, i + len(m.group(0))); j = n if j < 0 else j + len(close)
            else:
                j = i + (2 if c == 'b' else 1)
                while j < n and text[j] != '"':
                    j += 2 if text[j] == '\\' else 1
                j += 1
            for k in range(i, min(j, n)):
                if out[k] != '\n': out[k] = ' '
            i = j
        elif c == "'":
            m = re.match(r"'(?:\\.[^']*|[^'\\])'", text[i:i + 12])
            if m:
                for k in range(i, i + len(m.group(0))): out[k] = ' '
                i += len(m.group(0))
            else:
                i += 1
        else:
            i += 1
    return ''.join(out)


ATTR = re.compile(r'#!?\[\s*cfg\s*\(')


def sites(text):
    """[(attr line, cfg expression, extent first line, extent last line, inner attribute?)]"""
    b = blank(text)
    raw = text
    out = []
    for m in ATTR.finditer(b):
        # the expression: balanced parentheses from the `(` after cfg (taken from the raw text: strings matter here)
        i = m.end(); depth = 1
        while i < len(b) and depth:
            if b[i] == '(':
                depth += 1
            elif b[i] == ')':
                depth -= 1
            i += 1
        expr = raw[m.end():i - 1]
        j = b.find(']', i) + 1
        line = b.count('\n', 0, m.start()) + 1
        inner = b[m.start():m.start() + 2] == '#!'
        if inner:
            out.append((line, expr, line, b.count('\n') + 1, True))
            continue
        # skip whitespace and further attributes
        while True:
            while j < len(b) and b[j].isspace():
                j += 1
            if b.startswith('#[', j):
                d = 0
                while j < len(b):
                    if b[j] == '[': d += 1
                    elif b[j] == ']':
                        d -= 1
                        if d == 0: j += 1; break
                    j += 1
                continue
            break
        start = j; depth = 0; k = j; end = None
        while k < len(b):
            c = b[k]
            if c in '([{':
                depth += 1
            elif c in ')]}':
                depth -= 1
                if depth < 0:
                    end = k - 1; break
                if c == '}' and depth == 0:
                    # an item or block ends here unless `else` or `;` follows (if/else chains, `use a::{..};`)
                    rest = b[k + 1:k + 40].lstrip()
                    if rest.startswith('else'):
                        k += 1; continue
                    if rest.startswith(';'):
                        k = b.find(';', k); end = k; break
                    end = k; break
            elif c in ';,' and depth == 0:
                end = k; break
            k += 1
        if end is None:
            end = len(b) - 1
        out.append((line, expr, b.count('\n', 0, start) + 1, b.count('\n', 0, end) + 1, False))
    return out


def inactive(text, feats, target):
    rs = []
    for line, expr, a, z, inner in sites(text):
        try:
            v = value(parse(expr), feats, target)
        except Exception:
            v = None
        if v is False:
            rs.append((line, z))
    return rs


def compiled(ranges, line):
    return not any(a <= line <= z for a, z in ranges)


def compiled_files(tree, crate_dir, feats, target):
    """the source files (paths relative to the tree) that the crate's module tree compiles for one build: from
    src/lib.rs, every `mod NAME;` declaration that the build does not drop (inactive() of the declaring file), resolved
    to NAME.rs / NAME/mod.rs beside a lib.rs or mod.rs file (under STEM/ beside any other file), or to the
    `#[path = ".."]` given on the attribute lines directly above it (relative to the declaring file's directory)"""
    tree = Path(tree)
    root = tree / crate_dir / 'src' / 'lib.rs'
    out, stack = set(), [(root, True)]
    while stack:
        f, modrs = stack.pop()
        if not f.exists():
            continue
        rp = str(f.resolve().relative_to(tree.resolve())) if str(f.resolve()).startswith(str(tree.resolve())) else str(f)
        if rp in out:
            continue
        out.add(rp)
        text = f.read_text(errors='replace')
        L = text.split('\n')
        b = blank(text)
        ina = inactive(text, feats, target)
        for m in re.finditer(r'\bmod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;', b):
            ln = b.count('\n', 0, m.start()) + 1
            if not compiled(ina, ln):
                continue
            path = None
            j = ln - 2
            while j >= 0 and L[j].strip().startswith('#['):
                pm = re.search(r'#\[\s*path\s*=\s*"([^"]+)"', L[j])
                if pm:
                    path = pm.group(1)
                j -= 1
            if path:
                stack.append((f.parent / path, True))
            else:
                base = f.parent if modrs else f.parent / f.stem
                c1, c2 = base / (m.group(1) + '.rs'), base / m.group(1) / 'mod.rs'
                stack.append((c1, False) if c1.exists() else (c2, True))
    return out
