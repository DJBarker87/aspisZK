#!/usr/bin/env python3
"""X7: every Lean error of one native compile (fv_emit_native.sh), with the enclosing declaration of the raw file
(block rule of fv_emit_lean.py), its Rust path and source span, and the first line of the message. Reads only.
usage: fv_emit_errs.py <native dir> <ns>   (prints TSV; last line '# errors <n> in <k> declarations; modules ...')"""
import re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fv_emit_lean import blocks

D, NS = Path(sys.argv[1]), sys.argv[2]
print('module\tline\tdeclaration\trust_path\tsource\tmessage')
n, decls = 0, set()
for M in ('TypesExternal', 'Types', 'FunsExternal', 'Funs'):
    lg = D / (M + '.log')
    if not lg.exists():
        continue
    bl = blocks(D / 'src' / NS / (M + '.lean'))
    for m in re.finditer(r'^\S*?%s\.lean:(\d+):(\d+): error(?:\([^)]*\))?: ?(.*)$' % M, lg.read_text(errors='replace'), re.M):
        ln = int(m.group(1))
        b = next((x for x in reversed(bl) if x['first'] <= ln), None)
        name = b['lean'] if b else '?'
        decls.add((M, name))
        n += 1
        print('%s\t%d\t%s\t%s\t%s\t%s' % (M, ln, name, b['rust'] if b else '', '%s:%s-%s' % (b['file'], b['a'], b['b']) if b else '', m.group(3)[:200]))
ex = (D / 'exit.txt').read_text().strip().replace('\n', '; ') if (D / 'exit.txt').exists() else 'no exit.txt'
print('# errors %d in %d declarations; modules: %s' % (n, len(decls), ex))
