#!/usr/bin/env python3
# Pool final ELF: function-level comparison of two UNSTRIPPED SBF ELFs (the cargo target directory's
# copy, before cargo-build-sbf strips it). Each function's instructions are taken from
# `llvm-objdump -d --no-show-raw-insn`; the immediates of `call` and `lddw`, and jump targets printed as
# <symbol+offset>, are blanked so that a function that only moved, or calls a function that moved,
# compares equal. Prints the demangled names of functions present in only one ELF and of functions
# whose normalised body differs, with their instruction counts.
# Usage: python3 -I fv_pool_fndiff.py <llvm-objdump> <llvm-cxxfilt> <old.so> <new.so>
import re, subprocess, sys
from collections import OrderedDict
od, filt, a, b = sys.argv[1:5]

def functions(path):
    out = subprocess.run([od, '-d', '--no-show-raw-insn', path], capture_output=True, text=True).stdout
    fns = OrderedDict(); cur = None
    for line in out.splitlines():
        m = re.match(r'^[0-9a-f]+ <(.+)>:$', line)
        if m:
            cur = m.group(1); fns[cur] = []
            continue
        m = re.match(r'^\s*[0-9a-f]+:\s+(.*)$', line)
        if m and cur is not None:
            ins = m.group(1).strip()
            ins = re.sub(r'<[^>]*>', '<>', ins)
            if ins.startswith('call '):
                ins = 'call'
            elif ins.startswith('lddw '):
                ins = re.sub(r', .*$', ', IMM', ins)
            fns[cur].append(ins)
    return fns

def demangle(names):
    r = subprocess.run([filt], input='\n'.join(names), capture_output=True, text=True).stdout.splitlines()
    return dict(zip(names, r))

fa, fb = functions(a), functions(b)
# Strip the Rust hash suffix so that a function whose hash changed is matched by name.
key = lambda n: re.sub(r'17h[0-9a-f]{16}E$', 'E', n)
ka = {key(n): n for n in fa}; kb = {key(n): n for n in fb}
names = list(fa) + list(fb)
dm = demangle(names)
only_a = sorted(set(ka) - set(kb)); only_b = sorted(set(kb) - set(ka))
changed = [k for k in ka if k in kb and fa[ka[k]] != fb[kb[k]]]
print(f'functions: {len(fa)} in {a}, {len(fb)} in {b}')
print(f'only in old ({len(only_a)}):')
for k in only_a: print('  ', dm[ka[k]], len(fa[ka[k]]))
print(f'only in new ({len(only_b)}):')
for k in only_b: print('  ', dm[kb[k]], len(fb[kb[k]]))
print(f'normalised body differs ({len(changed)}):')
for k in changed: print('  ', dm[ka[k]], len(fa[ka[k]]), '->', len(fb[kb[k]]))
