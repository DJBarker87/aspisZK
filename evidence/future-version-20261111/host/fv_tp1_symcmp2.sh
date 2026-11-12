#!/bin/bash
# Aspis translatability pass: function-by-function comparison of two unstripped program ELFs given by path. Reads only.
# Lists function symbols on one side only or of different size (hash suffixes ignored; large sizes are printed in hex
# by readelf and read as such). Usage: fv_tp1_symcmp2.sh <control.so> <other.so>
python3 - "$1" "$2" <<'PY'
import subprocess, sys, re
a, b = sys.argv[1:3]
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
A, B = table(a), table(b)
print(f'.text bytes: control {text(a)}, other {text(b)}')
oa = sorted(set(A) - set(B)); ob = sorted(set(B) - set(A)); sz = sorted(k for k in A if k in B and A[k] != B[k])
print(f'function names {len(A)} (control) vs {len(B)} (other); only in control: {len(oa)} ({sum(sum(A[k]) for k in oa)} bytes); only in other: {len(ob)} ({sum(sum(B[k]) for k in ob)} bytes); different sizes: {len(sz)} (net {sum(sum(B[k])-sum(A[k]) for k in sz)} bytes)')
for k in oa: print('   only in control:', k[:170], A[k])
for k in ob: print('   only in other:  ', k[:170], B[k])
for k in sz: print('   size differs:   ', k[:170], A[k], '->', B[k])
PY
