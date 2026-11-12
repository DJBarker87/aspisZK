#!/bin/bash
# Naming cleanup (fz) copy of fv_tp1_r1cmp.sh (output in fz/r1cmp, receipts FZ-R1-*). Is the pinned R1 program intact inside a source tree?
# Builds the program from each named tree with R1's feature set (pool-adapter,private-leaf-salts) by the gate's own
# recipe and compares the ELF with devnet/verifier-pin2.so; where they differ, lists the functions whose size or
# bytes differ between the unstripped ELFs of the tree and of the first tree named (the control).
# Usage: fv_tp1_r1cmp.sh <control-tree> <tree>...      Time is expected in the SBF builds (cold target directories).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
O=$W/fz/r1cmp; mkdir -p $O; L=$O/result.txt; : > $L
for S in "$@"; do
  A=fz-r1-$S
  bash fv_slot.sh FZ-R1-$S 3000 bash $W/fv_build_adapter_src.sh $A pool-adapter,private-leaf-salts $S >> $O/build.log 2>&1
  E=$W/out/$A/artifacts/aspis_r1_cost_probe_program.so
  U=$W/target/sbf-adapter-$S/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so
  cp $U $O/unstripped-$S.so 2>/dev/null
  if cmp -s $E $W/devnet/verifier-pin2.so; then echo "$S: IDENTICAL to devnet/verifier-pin2.so ($(sha256sum $E | cut -c1-64))" >> $L
  else echo "$S: DIFFERS from devnet/verifier-pin2.so ($(stat -c %s $E 2>/dev/null) bytes, sha256 $(sha256sum $E 2>/dev/null | cut -c1-64); pin2 $(stat -c %s $W/devnet/verifier-pin2.so) bytes)" >> $L; fi
done
python3 - "$O" "$@" >> $L <<'PY'
import subprocess, sys, hashlib, re
O, trees = sys.argv[1], sys.argv[2:]
def table(p):
    out = subprocess.run(['readelf', '-sW', p], capture_output=True, text=True).stdout
    data = open(p, 'rb').read(); res = {}
    secs = subprocess.run(['readelf', '-SW', p], capture_output=True, text=True).stdout
    m = re.search(r'\.text\s+PROGBITS\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)', secs)
    addr, off = int(m.group(1), 16), int(m.group(2), 16)
    for l in out.splitlines():
        f = l.split()
        if len(f) >= 8 and f[3] == 'FUNC' and f[6] != 'UND':
            a, size = int(f[1], 16), int(f[2], 0)
            body = data[off + a - addr: off + a - addr + size]
            key = re.sub(r'17h[0-9a-f]{16}E$', '', f[7])   # the symbol without its hash suffix (the hash differs between trees)
            res.setdefault(key, []).append(size)
    return {k: tuple(sorted(v)) for k, v in res.items()}
base = table(f'{O}/unstripped-{trees[0]}.so')
for t in trees[1:]:
    cur = table(f'{O}/unstripped-{t}.so')
    only_a = sorted(set(base) - set(cur)); only_b = sorted(set(cur) - set(base))
    size = sorted(k for k in base if k in cur and base[k] != cur[k])
    print(f'{t} against {trees[0]}: function names {len(cur)} vs {len(base)}; only in {trees[0]}: {len(only_a)}; only in {t}: {len(only_b)}; different sizes: {len(size)} (bytes of equal-sized functions are not compared: call offsets move)')
    for k in only_a[:25]: print('   only in control:', k[:150], base[k])
    for k in only_b[:25]: print('   only in tree:   ', k[:150], cur[k])
    for k in size[:40]: print('   size differs:   ', k[:150], base[k], '->', cur[k])
PY
echo DONE >> $L
