#!/usr/bin/env python3
"""NPP_: offline check of the probe's pda binder. Usage: python3 -I NPP_check_pda.py <stdout.log> [recorded keys...]
Recomputes every `NPP_PDA [seeds] program answer` line with hashlib and an independent ed25519
on-curve test (pure Python), and reports which answers are keys of the recorded transaction."""
import sys, hashlib, json, re
P = 2**255 - 19; D = (-121665 * pow(121666, P - 2, P)) % P
def on_curve(h):
    y = int.from_bytes(h, 'little') & ((1 << 255) - 1); y %= P
    u = (y * y - 1) % P; v = (D * y * y + 1) % P
    x2 = u * pow(v, P - 2, P) % P
    return x2 == 0 or pow(x2, (P - 1) // 2, P) == 1
def create(seeds, prog):
    if len(seeds) > 16 or any(len(s) > 32 for s in seeds): return None
    h = hashlib.sha256(b''.join(seeds) + prog + b'ProgramDerivedAddress').digest()
    return None if on_curve(h) else h
keys = set(sys.argv[2:])
rows = []
for line in open(sys.argv[1]):
    if not line.startswith('NPP_PDA '): continue
    m = re.match(r'NPP_PDA \[(.*)\] (\S+) (\S+)', line.strip())
    seeds = [bytes.fromhex(x.strip()) for x in m.group(1).split(',') if x.strip()]
    prog = bytes.fromhex(m.group(2)); ans = m.group(3)
    ref = create(seeds, prog); refh = ref.hex() if ref else 'none'
    rows.append({'seeds': [s.hex() for s in seeds], 'program': prog.hex(), 'answer': ans, 'recomputed': refh,
                 'agree': ans == refh, 'is_recorded_key': ans in keys})
print(json.dumps({'queries': len(rows), 'all_agree': all(r['agree'] for r in rows), 'rows': rows}, indent=1))
