#!/bin/bash
# Aspis translatability pass: which functions differ between the unstripped program ELFs of two source trees?
# Copies the two unstripped ELFs (as last built in target/sbf-adapter-<tree>) under tp1/symcmp/<label>/ and lists
# the function symbols present on one side only or of different size (the hash suffix of each symbol is ignored;
# bytes of equal-sized functions are not compared because call offsets move). Reads only; no build.
# Usage: fv_tp1_symcmp.sh <label> <control-tree> <tree>
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
O=$W/tp1/symcmp/$1; mkdir -p $O
for S in $2 $3; do cp $W/target/sbf-adapter-$S/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so $O/unstripped-$S.so || exit 1; sha256sum $O/unstripped-$S.so; done > $O/result.txt
python3 - "$O" $2 $3 >> $O/result.txt <<'PY'
import subprocess, sys, re
O, a, b = sys.argv[1:4]
def table(p):
    out = subprocess.run(['readelf', '-sW', p], capture_output=True, text=True).stdout
    res = {}
    for l in out.splitlines():
        f = l.split()
        if len(f) >= 8 and f[3] == 'FUNC' and f[6] != 'UND':
            key = re.sub(r'17h[0-9a-f]{16}E$', '', f[7])
            res.setdefault(key, []).append(int(f[2], 0))
    return {k: tuple(sorted(v)) for k, v in res.items()}
def text(p):
    secs = subprocess.run(['readelf', '-SW', p], capture_output=True, text=True).stdout
    m = re.search(r'\.text\s+PROGBITS\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)', secs)
    return int(m.group(3), 16)
A, B = table(f'{O}/unstripped-{a}.so'), table(f'{O}/unstripped-{b}.so')
print(f'.text bytes: {a} {text(O+"/unstripped-"+a+".so")}, {b} {text(O+"/unstripped-"+b+".so")}')
oa = sorted(set(A) - set(B)); ob = sorted(set(B) - set(A)); sz = sorted(k for k in A if k in B and A[k] != B[k])
print(f'function names {len(A)} ({a}) vs {len(B)} ({b}); only in {a}: {len(oa)} ({sum(sum(A[k]) for k in oa)} bytes); only in {b}: {len(ob)} ({sum(sum(B[k]) for k in ob)} bytes); different sizes: {len(sz)} (net {sum(sum(B[k])-sum(A[k]) for k in sz)} bytes)')
for k in oa: print('   only in control:', k[:170], A[k])
for k in ob: print('   only in tree:   ', k[:170], B[k])
for k in sz: print('   size differs:   ', k[:170], A[k], '->', B[k])
PY
cat $O/result.txt | cut -c1-260
