#!/usr/bin/env python3
"""Aspis freeze: per-function line ranges and body hashes of two Pool source files at two revisions.
For every `fn` whose line starts at column 0 or inside an `impl` (not inside a `mod tests`-style test module):
  lines_fn  = from the `fn` line to the closing brace at the same indentation;
  sha_fn    = sha256 of that text with a trailing newline (the convention of POOL-PAGE-CHECK.md);
  lines_att = the same range extended upwards over attribute lines (`#[...]`);
  sha_att   = sha256 of that text with a trailing newline (the convention of translatability/core/tp3_fnranges.py).
Doc comments are in neither range. Reads Git only (`git show <rev>:<file>`).
usage: pool_fn_changes.py <revA> <revB> <out.tsv> <file>...   (run from the repository root)"""
import hashlib, re, subprocess, sys
A, B, OUT = sys.argv[1:4]; FILES = sys.argv[4:]
PAT = re.compile(r'^(\s*)(pub(\([a-z]+\))? )?(const )?(unsafe )?fn ([A-Za-z0-9_]+)\b')
def table(rev, f):
    lines = subprocess.run(['git', 'show', f'{rev}:{f}'], capture_output=True, text=True, check=True).stdout.split('\n')
    cut = next((i for i, l in enumerate(lines) if re.match(r'^(#\[cfg\(test\)\]|mod [a-z_]*tests?\b)', l)), len(lines))
    out = {}; seen = {}
    for i, l in enumerate(lines[:cut]):
        m = PAT.match(l)
        if not m: continue
        ind, name = m.group(1), m.group(6)
        j = i
        while j < len(lines) and not (lines[j].startswith(ind + '}') and len(lines[j].rstrip()) == len(ind) + 1):
            if ';' in lines[j] and '{' not in ''.join(lines[i:j + 1]): break   # a declaration without a body
            j += 1
        if j >= len(lines) or not lines[j].startswith(ind + '}'): continue
        s = i
        while s > 0 and lines[s - 1].strip().startswith('#['): s -= 1
        h = lambda a, b: hashlib.sha256(('\n'.join(lines[a:b + 1]) + '\n').encode()).hexdigest()
        seen[name] = seen.get(name, 0) + 1
        out[f'{name}#{seen[name]}'] = (f'{i + 1}-{j + 1}', h(i, j), f'{s + 1}-{j + 1}', h(s, j))
    return out
rows = ['file\tfunction\tstatus\tlines_fn_A\tsha_fn_A\tlines_fn_B\tsha_fn_B\tlines_att_B\tsha_att_B']
summary = []
for f in FILES:
    a, b = table(A, f), table(B, f); n = {'new': 0, 'body changed': 0, 'moved only': 0, 'unchanged': 0, 'removed': 0}
    for k in sorted(set(a) | set(b), key=lambda k: int((b.get(k) or a.get(k))[0].split('-')[0])):
        x, y = a.get(k), b.get(k)
        st = 'new' if x is None else 'removed' if y is None else 'body changed' if x[1] != y[1] else 'moved only' if x[0] != y[0] else 'unchanged'
        n[st] += 1
        if st != 'unchanged':
            rows.append('\t'.join([f, k.split('#')[0] + ('' if k.endswith('#1') else k[k.index('#'):]), st, x[0] if x else '-', x[1] if x else '-', y[0] if y else '-', y[1] if y else '-', y[2] if y else '-', y[3] if y else '-']))
    summary.append(f'{f}: ' + ', '.join(f'{v} {k}' for k, v in n.items()))
open(OUT, 'w').write('\n'.join(rows) + '\n'); print('\n'.join(summary))
