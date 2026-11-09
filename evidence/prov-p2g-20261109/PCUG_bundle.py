#!/usr/bin/env python3
"""PCUG_bundle.py: concatenate several generated PRVEq_<M>.lean files into one compile vehicle (one Lean scope).
The bundle is the exact text of each file: imports are hoisted and de-duplicated, every file body is wrapped in
`section PRVBundle_i ... end PRVBundle_i` (a file's own `noncomputable section` is closed first), and the 1-based line
offset of each file body is written next to the bundle so that PCUG_gen_equalities.py --line-offset can map the Lean log
back to the module. Usage: PCUG_bundle.py OUT.lean OFFSETS.json PRVEq_A.lean PRVEq_B.lean ..."""
import sys, json, re
from pathlib import Path
out, offs, *files = sys.argv[1:]
imports = []; body = []; offsets = {}
for i, f in enumerate(files):
    lines = Path(f).read_text().split('\n'); keep = []
    for l in lines:
        if l.startswith('import '):
            if l not in imports: imports.append(l)
        else: keep.append(l)
    noncomp = any(l.strip() == 'noncomputable section' for l in keep)
    body.append(f'section PRVBundle_{i}')
    offsets[Path(f).stem] = dict(module_file=f, offset=len(body) and sum(len(b.split('\n')) for b in body), index=i)
    body.append('\n'.join(keep))
    if noncomp: body.append('end')
    body.append(f'end PRVBundle_{i}')
imps = [l for l in imports if l == 'import Aeneas'] + [l for l in imports if l != 'import Aeneas']
header = ['-- PRV bundle (compile vehicle only): exact concatenation of ' + ', '.join(Path(f).name for f in files)] + imps + ['set_option maxErrors 100000  -- PCT patch: the default 100 stops a probe bundle early', '']
text = '\n'.join(header) + '\n'.join(body) + '\n'
# recompute offsets against the final text: first line of each file body is the line after its `section PRVBundle_i`
ls = text.split('\n')
for i, f in enumerate(files):
    k = ls.index(f'section PRVBundle_{i}')
    offsets[Path(f).stem]['offset'] = k + 1 - 0  # body line j of the module file is bundle line k+1+(j - first kept line)
Path(out).write_text(text)
# the module file had its import lines removed: store removed-count before each line to map exactly
for i, f in enumerate(files):
    src = Path(f).read_text().split('\n'); k = ls.index(f'section PRVBundle_{i}')
    mapping = []; n = 0
    for j, l in enumerate(src, 1):
        if l.startswith('import '): continue
        n += 1; mapping.append((j, k + 1 + n))
    offsets[Path(f).stem]['line_map'] = mapping
Path(offs).write_text(json.dumps(offsets))
print(out, len(ls), 'lines')
