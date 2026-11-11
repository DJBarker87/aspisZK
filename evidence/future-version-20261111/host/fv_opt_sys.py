#!/usr/bin/env python3
"""Optimisation rounds: executed syscall sites by syscall name and by enclosing function.

usage: fv_opt_sys.py <linked-unstripped.so> <trace.regs> <readelf> <out.json>
Relocations name the syscall at each call site; the trace counts how often each site ran.
Attribution evidence only.
"""
import array, collections, json, re, subprocess, sys
sys.path.insert(0, '/home/dombarker/project-offloads/future-version-20261111')
from fv_profile import sections, functions, demangle, short

elf, regs_path, readelf, out_path = sys.argv[1:5]
data = open(elf, 'rb').read()
secs = sections(data)
text = next(s for s in secs if s['name'] == '.text')
regs = array.array('Q')
regs.frombytes(open(regs_path, 'rb').read())
pcs = regs[11::12]
count = collections.Counter(pcs)
funcs = functions(data, secs)
import bisect
starts = [f[0] for f in funcs]
def func_of(a):
    k = bisect.bisect_right(starts, a) - 1
    return short(demangle(funcs[k][2])) if k >= 0 and a < funcs[k][0] + funcs[k][1] else '?'
rel = subprocess.run([readelf, '-r', '--wide', elf], capture_output=True, text=True).stdout
by_name = collections.Counter(); by_site = collections.Counter()
for l in rel.split('\n'):
    m = re.match(r'\s*([0-9a-f]+)\s+[0-9a-f]+\s+(\S+)\s+[0-9a-f]+\s+(\S+)', l)
    if not m or not m.group(3).startswith(('sol_', 'abort', 'custom_panic')):
        continue
    off = int(m.group(1), 16)
    pc = (off - text['addr']) // 8 if off >= text['addr'] else (off - text['offset']) // 8
    c = count.get(pc, 0)
    if c:
        by_name[m.group(3)] += c
        by_site[(m.group(3), func_of(text['addr'] + 8 * pc))] += c
json.dump({'by_name': by_name.most_common(), 'by_site': [[a, b, c] for (a, b), c in by_site.most_common()]}, open(out_path, 'w'), indent=1)
print(by_name.most_common())
