#!/usr/bin/env python3
"""Optimisation rounds: hot loops of a stripped program from a register trace (no symbols needed).

usage: fv_opt_loops.py <program.so> <trace.regs> <objdump> [min-count]
Groups consecutive executed instructions with the same execution count (a loop body shows up as a run
of equal counts) and prints the runs that account for the most instructions, with their disassembly.
Attribution evidence only.
"""
import array, collections, re, subprocess, sys
sys.path.insert(0, '/home/dombarker/project-offloads/future-version-20261111')
from fv_profile import sections
elf, regs_path, objdump = sys.argv[1:4]
minc = int(sys.argv[4]) if len(sys.argv) > 4 else 200
data = open(elf, 'rb').read()
text = next(s for s in sections(data) if s['name'] == '.text')
regs = array.array('Q'); regs.frombytes(open(regs_path, 'rb').read())
pcs = regs[11::12]
count = collections.Counter(pcs)
n = len(pcs)
dis = {}
for l in subprocess.run([objdump, '-d', '--no-show-raw-insn', elf], capture_output=True, text=True).stdout.split('\n'):
    m = re.match(r'\s*([0-9a-f]+):\s+(.*)', l)
    if m: dis[int(m.group(1), 16)] = m.group(2)
runs = []
cur = None
for pc in sorted(count):
    c = count[pc]
    if cur and pc == cur['end'] + 1 and c == cur['count']:
        cur['end'] = pc
    else:
        cur = dict(start=pc, end=pc, count=c); runs.append(cur)
for r in runs: r['total'] = r['count'] * (r['end'] - r['start'] + 1)
print(f'executed instructions {n}')
hot = sorted([r for r in runs if r['count'] >= minc], key=lambda r: -r['total'])
for r in hot[:25]:
    a0 = text['addr'] + 8 * r['start']
    print(f"== count {r['count']} x {r['end'] - r['start'] + 1} instructions = {r['total']}  at {a0:#x}")
    for pc in range(r['start'], r['end'] + 1):
        print('      ', dis.get(text['addr'] + 8 * pc, '?'))
