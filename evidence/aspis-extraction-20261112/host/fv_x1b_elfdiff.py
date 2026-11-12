#!/usr/bin/env python3
"""X1b: per-function instruction counts of two SBF ELFs from `llvm-objdump -d --no-show-raw-insn` text (functions are
the `<symbol>:` blocks; instructions are the lines with an address), and the functions whose count or instruction
text (addresses and branch targets removed) differs. Also the total instruction count and the byte difference of
.rodata is not read here.
usage: fv_x1b_elfdiff.py <objdump A> <objdump B>   (prints TSV: function, count A, count B, delta, text differs)"""
import re, sys
def funcs(path):
    out = {}; cur = None
    for l in open(path, errors='replace'):
        m = re.match(r'^[0-9a-f]+ <(.+)>:\s*$', l)
        if m: cur = m.group(1); out.setdefault(cur, []); continue
        m = re.match(r'^\s+[0-9a-f]+:\s+(.*)$', l)
        if m and cur is not None:
            ins = re.sub(r'\s+', ' ', m.group(1)).strip()
            ins = re.sub(r'\b(0x)?[0-9a-f]{6,}\b', 'A', ins); ins = re.sub(r'<[^>]*>', '<>', ins)
            ins = re.sub(r'([+-])\s*\d+\b', r'\1N', ins) if ins.startswith(('ja', 'j', 'call')) else ins
            out[cur].append(ins)
    return out
A, B = funcs(sys.argv[1]), funcs(sys.argv[2])
ta, tb = sum(map(len, A.values())), sum(map(len, B.values()))
print('function\tcount_a\tcount_b\tdelta\ttext_differs')
rows = []
for f in sorted(set(A) | set(B)):
    a, b = A.get(f), B.get(f)
    if a == b: continue
    rows.append((f, len(a) if a is not None else -1, len(b) if b is not None else -1, (len(b) if b else 0) - (len(a) if a else 0), 'yes'))
for r in sorted(rows, key=lambda r: -abs(r[3])): print('%s\t%d\t%d\t%+d\t%s' % r)
print('# functions A %d, B %d; instructions A %d, B %d (%+d); differing functions %d' % (len(A), len(B), ta, tb, tb - ta, len(rows)))
