#!/usr/bin/env python3
"""X7: whether the 32-byte values of the given base58 program ids (the deployment ids the SBF build was given), and
of the SDK loader id bpf_loader_upgradeable, occur in a built verifier ELF, and at which offsets. Reads only.
usage: fv_emit_elfids.py <elf> <base58 id>..."""
import sys
A = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def b58(s):
    n = 0
    for ch in s: n = n * 58 + A.index(ch)
    raw = n.to_bytes((n.bit_length() + 7) // 8, 'big') if n else b''
    return b'\0' * (len(s) - len(s.lstrip('1'))) + raw
elf = open(sys.argv[1], 'rb').read()
for s in sys.argv[2:] + ['BPFLoaderUpgradeab1e11111111111111111111111']:
    v = b58(s); offs = []; k = elf.find(v)
    while k >= 0: offs.append(k); k = elf.find(v, k + 1)
    print('%s %s occurrences %d offsets %s' % (s, v.hex(), len(offs), ','.join(hex(o) for o in offs)))
