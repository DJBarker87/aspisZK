#!/usr/bin/env python3
"""Optimisation rounds: executed-instruction counts per address, written beside the disassembly.

usage: fv_opt_hot.py <linked-unstripped.so> <trace.regs> <objdump> <out.txt> <symbol-substring>...

For every function symbol whose demangled-ish name contains one of the substrings, prints each
instruction with the number of times it was executed in the trace. Attribution evidence only.
"""
import array, collections, re, subprocess, sys
sys.path.insert(0, '/home/dombarker/project-offloads/future-version-20261111')
from fv_profile import sections, functions, demangle

elf, regs_path, objdump, out_path = sys.argv[1:5]
subs = sys.argv[5:]
data = open(elf, 'rb').read()
secs = sections(data)
text = next(s for s in secs if s['name'] == '.text')
regs = array.array('Q')
regs.frombytes(open(regs_path, 'rb').read())
pcs = regs[11::12]
count = collections.Counter(pcs)
funcs = functions(data, secs)
dis = subprocess.run([objdump, '-d', '--no-show-raw-insn', '-l', elf], capture_output=True, text=True).stdout
lines = dis.split('\n')
with open(out_path, 'w') as out:
    for (start, size, name) in funcs:
        dn = demangle(name)
        if not any(s in dn for s in subs):
            continue
        total = sum(count.get((a - text['addr']) // 8, 0) for a in range(start, start + size, 8))
        out.write(f'==== {dn} @{start:#x} size {size} executed {total}\n')
        inside = False
        for l in lines:
            m = re.match(r'\s*([0-9a-f]+):\s+(.*)', l)
            if m:
                a = int(m.group(1), 16)
                if start <= a < start + size:
                    c = count.get((a - text['addr']) // 8, 0)
                    out.write(f'{c:8d}  {a:#x}: {m.group(2)}\n')
                    inside = True
                elif inside and a >= start + size:
                    break
            elif inside and l.strip() and not l.startswith('Disassembly'):
                out.write(f'          {l.strip()}\n')
print('ok')
