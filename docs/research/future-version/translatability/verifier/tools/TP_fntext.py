#!/usr/bin/env python3
"""Aspis translatability pass: function-level text comparison of two revisions (or a revision and a directory).
For every `fn` in the listed files: its text from the start of its first attribute/doc line to the closing brace of
its body, keyed by (file, enclosing impl/mod/fn chain, name, ordinal). Reads Git with `git show` only.
usage: TP_fntext.py <revA> <revB|dir:PATH> <json-out> <file>...   (run from the repository root)"""
import json, re, subprocess, sys, hashlib
from pathlib import Path
A, B, OUT = sys.argv[1:4]; FILES = sys.argv[4:]
def load(rev, f):
    if rev.startswith('dir:'):
        p = Path(rev[4:]) / f; return p.read_text() if p.exists() else None
    r = subprocess.run(['git', 'show', rev + ':' + f], capture_output=True)
    return r.stdout.decode() if r.returncode == 0 else None
def strip(src):
    """same length as src, with comments, strings and char literals blanked (so that braces in them do not count)"""
    out = list(src); i = 0; n = len(src)
    def blank(a, b):
        for k in range(a, b):
            if out[k] != '\n': out[k] = ' '
    while i < n:
        c = src[i]
        if src.startswith('//', i):
            j = src.find('\n', i); j = n if j < 0 else j; blank(i, j); i = j
        elif src.startswith('/*', i):
            d = 1; j = i + 2
            while j < n and d:
                if src.startswith('/*', j): d += 1; j += 2
                elif src.startswith('*/', j): d -= 1; j += 2
                else: j += 1
            blank(i, j); i = j
        elif c == '"' or (c in 'rb' and re.match(r'(?:b?r#*"|b")', src[i:])):
            m = re.match(r'b?r(#*)"', src[i:])
            if m:
                end = src.find('"' + m.group(1), i + len(m.group(0))); j = (end + 1 + len(m.group(1))) if end >= 0 else n
            else:
                j = i + (2 if c == 'b' else 1)
                while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
                j += 1
            blank(i + 1, j - 1); i = j
        elif c == "'" :
            m = re.match(r"'(?:\\.[^']*|[^'\\])'", src[i:])
            if m: blank(i + 1, i + len(m.group(0)) - 1); i += len(m.group(0))
            else: i += 1
        else: i += 1
    return ''.join(out)
def fns(src):
    s = strip(src); res = {}; stack = []; depth = 0; pending = None; counts = {}
    toks = list(re.finditer(r'[{};()\[\]]|\bfn\s+([A-Za-z_][A-Za-z0-9_]*)|\b(impl|mod|trait)\b([^{;]*)', s))
    par = 0
    lines = src.split('\n'); starts = [0]
    for l in lines: starts.append(starts[-1] + len(l) + 1)
    def line_of(pos):
        import bisect; return bisect.bisect_right(starts, pos) - 1
    for m in toks:
        t = m.group(0)
        if m.group(1):
            pending = ('fn', m.group(1), m.start())
        elif m.group(2):
            pending = ('ctx', (m.group(2) + ' ' + ' '.join(m.group(3).split()))[:60], m.start())
        elif t == '{':
            depth += 1; par = 0
            if pending: stack.append((pending, depth)); pending = None
        elif t in '([':
            par += 1
        elif t in ')]':
            par = max(0, par - 1)
        elif t == ';':
            if par == 0: pending = None
        elif t == '}':
            if stack and stack[-1][1] == depth:
                (kind, name, pos), _ = stack.pop()
                if kind == 'fn':
                    ln = line_of(pos); a = ln
                    while a > 0 and re.match(r'\s*(#\[|///|//!|#!\[)', lines[a - 1]): a -= 1
                    text = src[starts[a]:m.end()]
                    ctx = '/'.join(x[0][1] for x in stack)
                    k0 = (ctx, name); counts[k0] = counts.get(k0, 0) + 1
                    nocfg = '\n'.join(l for l in text.split('\n') if not re.match(r'\s*#\[cfg\(', l))
                    cfgs = [l.strip() for l in text.split('\n') if re.match(r'\s*#\[cfg\(', l) and text.index(l) < text.index('fn ' + name)]
                    res['%s::%s#%d' % (ctx, name, counts[k0])] = dict(text=text, nocfg=nocfg, cfg=cfgs, line=ln + 1)
            depth -= 1
    return res
rep = {}
for f in FILES:
    a, b = load(A, f), load(B, f)
    fa = fns(a) if a is not None else {}; fb = fns(b) if b is not None else {}
    for k in sorted(set(fa) | set(fb)):
        ta = fa.get(k, {}).get('text'); tb = fb.get(k, {}).get('text')
        na = fa.get(k, {}).get('nocfg'); nb = fb.get(k, {}).get('nocfg')
        st = 'not present at A' if ta is None else 'removed at B' if tb is None else 'identical' if ta == tb else 'identical under an added cfg attribute' if na == nb else ('whitespace only' if ''.join(ta.split()) == ''.join(tb.split()) else 'CHANGED')
        rep[f + '|' + k] = dict(status=st, cfg_b=fb.get(k, {}).get('cfg'), line_a=fa.get(k, {}).get('line'), line_b=fb.get(k, {}).get('line'),
                                sha_a=hashlib.sha256(ta.encode()).hexdigest()[:16] if ta else None, sha_b=hashlib.sha256(tb.encode()).hexdigest()[:16] if tb else None)
json.dump(rep, open(OUT, 'w'), indent=0)
import collections
print(collections.Counter(v['status'] for v in rep.values()))
for k, v in rep.items():
    if v['status'] in ('CHANGED', 'removed at B', 'whitespace only', 'identical under an added cfg attribute'): print('%-40s %s (A line %s) %s' % (v['status'], k, v['line_a'], ' '.join(v.get('cfg_b') or [])))
