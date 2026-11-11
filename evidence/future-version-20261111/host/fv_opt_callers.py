#!/usr/bin/env python3
"""Optimisation rounds: who calls a given outlined function (by call-site function and source line).

usage: fv_opt_callers.py <linked-unstripped.so> <trace.regs> <callee-substring>...
Attribution evidence only.
"""
import array, bisect, collections, subprocess, sys
sys.path.insert(0, '/home/dombarker/project-offloads/future-version-20261111')
from fv_profile import sections, functions, demangle, short

elf, regs_path = sys.argv[1:3]
subs = sys.argv[3:]
data = open(elf, 'rb').read()
secs = sections(data)
text = next(s for s in secs if s['name'] == '.text')
tb = data[text['offset']:text['offset'] + text['size']]
regs = array.array('Q'); regs.frombytes(open(regs_path, 'rb').read())
pcs = regs[11::12]
funcs = functions(data, secs)
starts = [f[0] for f in funcs]
def func_of(a):
    k = bisect.bisect_right(starts, a) - 1
    return demangle(funcs[k][2]) if k >= 0 and a < funcs[k][0] + funcs[k][1] else '?'
sites = collections.Counter()
for i in range(len(pcs) - 1):
    pc = pcs[i]
    if tb[8 * pc] in (0x85, 0x8d) and pcs[i + 1] != pc + 1:
        callee = func_of(text['addr'] + 8 * pcs[i + 1])
        if any(s in callee for s in subs):
            sites[(callee, text['addr'] + 8 * pc)] += 1
addrs = sorted({a for (_, a) in sites})
out = subprocess.run(['addr2line', '-e', elf, '-f', '-i', '-a'] , input='\n'.join(hex(a) for a in addrs), capture_output=True, text=True).stdout
info = {}; cur = None
for l in out.split('\n'):
    if l.startswith('0x'):
        cur = int(l, 16); info[cur] = []
    elif cur is not None and l:
        info[cur].append(l)
for (callee, a), c in sites.most_common(60):
    chain = info.get(a, [])
    where = ' <- '.join(short(demangle(chain[k])) + '@' + chain[k + 1].split('/')[-1] for k in range(0, min(len(chain), 8), 2))
    print(c, short(callee), hex(a), where)
