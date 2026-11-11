#!/usr/bin/env python3
# Pool page zero check: in a Pool ELF, find each function that contains a sol_memcmp_ syscall site (the
# R_SBF_64_32 relocation), take the start of that function (the instruction after the previous `exit`),
# and count the `call` instructions whose relative target is that start. Prints, per ELF, the syscall
# sites and the number of call sites of each wrapper.
# Usage: python3 -I fv_pool_memcmp_calls.py <llvm-objdump> <llvm-readelf> <elf>...
import re, subprocess, sys
od = sys.argv[1]
re_ = sys.argv[2]
for elf in sys.argv[3:]:
    dis = subprocess.run([od, '-d', '-r', elf], capture_output=True, text=True).stdout.splitlines()
    ins = []  # (addr, text)
    sites = []
    for line in dis:
        m = re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} ){8})\s*(.*)$', line)
        if m:
            ins.append((int(m.group(1), 16), m.group(3).strip()))
    for line in subprocess.run([re_, '-r', elf], capture_output=True, text=True).stdout.splitlines():
        if 'R_SBF_64_32' in line and line.rstrip().endswith('sol_memcmp_'):
            sites.append(int(line.split()[0], 16))
    index = {a: i for i, (a, _) in enumerate(ins)}
    starts = []
    for s in sites:
        i = index[s]
        while i > 0 and not ins[i - 1][1].startswith('exit'):
            i -= 1
        starts.append(ins[i][0])
    counts = {st: 0 for st in starts}
    for a, t in ins:
        m = re.match(r'^call (-?0x[0-9a-f]+)$', t)
        if m:
            target = a + 8 + int(m.group(1), 16) * 8
            if target in counts:
                counts[target] += 1
    print(elf)
    print('  sol_memcmp_ syscall sites:', [hex(s) for s in sites])
    for st in starts:
        print(f'  function at {st:#x} (contains a syscall site): {counts[st]} call sites')
