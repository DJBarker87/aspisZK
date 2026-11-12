#!/usr/bin/env python3
"""X7 helper (imported by the other fv_emit_* scripts; reads only): a parser for the RAW Aeneas Lean output of
Charon 454586e9 / Aeneas 0d21a9ec. Every declaration is a block: a doc comment `/-- [rust path]: <label>` with
`Source: '<file>', lines a:c-b:d`, optional `Name pattern:` and `Visibility:` lines, attribute lines, then the
declaration keyword and its Lean name. The block runs to the next doc comment (or the end of the namespace).

blocks(path) -> list of dicts: rust, label, file, a, b, lean, kind, first, last (1-based lines of the block),
                                 decl (line of the keyword), text (the block's lines without the doc comment)."""
import re
from pathlib import Path

DOC = re.compile(r'^/-- (?:([A-Z][a-z]+(?: [a-z]+)*): )?\[(.*)\](?::\s*(.*?))?\s*(?:-/)?$')   # greedy: Rust paths hold `[T; N]`
SRC = re.compile(r"Source: '([^']*)', lines (\d+):\d+-(\d+):\d+")
KIND = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|partial\s+|private\s+|protected\s+|unsafe\s+|divergent\s+)*'
                  r'(def|axiom|opaque|structure|inductive|instance|theorem|abbrev|impl_def)\b\s*(\S*)')
ASPIS_DIRS = (('crates/aspis-core/', 'aspis_core'), ('crates/aspis-statement/', 'aspis_statement'),
              ('crates/aspis-r1-cost-probe/', 'aspis_r1_cost_probe'), ('programs/r1-cost-probe/', 'aspis_r1_cost_probe_program'),
              ('programs/aspis-pool/', 'aspis_pool'))
ASPIS_CRATES = tuple(c for _, c in ASPIS_DIRS)


def rel(path, tree=None):
    """a source path relative to the tree root (Charon writes absolute or relative paths)"""
    if not path:
        return path
    if tree and path.startswith(str(tree).rstrip('/') + '/'):
        return path[len(str(tree).rstrip('/')) + 1:]
    for d, _ in ASPIS_DIRS:
        k = path.find('/' + d)
        if k >= 0 and not path.startswith(d):
            return path[k + 1:]
    return path


def crate_of(file, rust=''):
    for d, c in ASPIS_DIRS:
        if file and rel(file).startswith(d):
            return c
    head = re.split(r'::|\{|<|\[|\s', (rust or '').lstrip('{[<&\'0 '), 1)[0]
    if head in ASPIS_CRATES:
        return head
    return None


def blocks(path):
    p = Path(path)
    if not p.exists():
        return []
    L = p.read_text().split('\n')
    out = []
    starts = [i for i, l in enumerate(L) if l.startswith('/-- ')]
    ends = starts[1:] + [len(L)]
    for s, e in zip(starts, ends):
        m = DOC.match(L[s])
        rust, label = (m.group(2), ' '.join(x.rstrip(':') for x in (m.group(1), m.group(3)) if x)) if m else ('', '')
        j = s
        while j < e and '-/' not in L[j]:
            j += 1
        doc = '\n'.join(L[s:j + 1])
        sm = SRC.search(doc)
        k = j + 1
        decl, kind, lean = None, None, None
        while k < e:
            km = KIND.match(L[k])
            if km:
                decl, kind, lean = k, km.group(1), km.group(2)
                if not lean and k + 1 < e:
                    lean = L[k + 1].strip().split()[0] if L[k + 1].strip() else ''
                break
            k += 1
        last = e
        while last > s and (not L[last - 1].strip() or L[last - 1].startswith('end ')):
            last -= 1
        out.append(dict(rust=rust, label=label, file=sm.group(1) if sm else '', a=int(sm.group(2)) if sm else None,
                        b=int(sm.group(3)) if sm else None, lean=lean or '', kind=kind or '', first=s + 1, last=last,
                        decl=(decl + 1) if decl is not None else None, text='\n'.join(L[j + 1:last])))
    return out


def item_extent(tree, f, a, b):
    """X1's rule (fv_x1_rows.py item_extent): the doc comment's line range when it spans more than one line; when it
    names one line only, the item from that line to the closing brace of its body (or the `;` of a constant), by
    brace matching after blanking comments, strings and character literals"""
    p = Path(tree) / f
    if not f or not a or not p.exists():
        return None, None
    b = b or a
    if b > a:
        return a, b
    L = p.read_text(errors='replace').split('\n')
    depth = 0
    seen = False
    for i in range(a - 1, len(L)):
        s = re.sub(r'//.*', '', L[i])
        s = re.sub(r'"(?:\\.|[^"\\])*"', '""', s)
        s = re.sub(r"'(?:\\.|[^'\\])'", "''", s)
        for c in s:
            if c in '{([':
                depth += 1
                seen = seen or c == '{'
            elif c in '})]':
                depth -= 1
            elif c == ';' and depth == 0:
                return a, i + 1
        if seen and depth == 0:
            return a, i + 1
    return a, a
