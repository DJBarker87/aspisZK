#!/usr/bin/env python3
"""Pure-Python find_program_address (Ed25519 decompress predicate as in
curve25519-dalek 4: y = bytes LE with bit 255 masked, reduced mod p; on curve
iff (y^2-1)/(d*y^2+1) is a square or zero). Used only to pick a lane/page whose
OLD canonical page search needed many attempts (the driver's seed grind cannot
vary the page address at a fixed --pairs: only 8 lanes). Cross-checked below
against bumps recorded by the LiteSVM driver.
usage: pda_search.py <min_attempts> <max_page>"""
import hashlib, struct, sys
p = 2**255 - 19
d = (-121665 * pow(121666, p - 2, p)) % p
def on_curve(h):
    y = int.from_bytes(h, 'little') & ((1 << 255) - 1)
    y %= p
    u = (y * y - 1) % p; v = (d * y * y + 1) % p
    r = u * pow(v, p - 2, p) % p
    return r == 0 or pow(r, (p - 1) // 2, p) == 1
def find_pda(seeds, program):
    for bump in range(255, 0, -1):
        h = hashlib.sha256(b''.join(seeds) + bytes([bump]) + program + b'ProgramDerivedAddress').digest()
        if not on_curve(h):
            return h, bump
    raise ValueError
prog = bytes([0x41] * 32); mint = bytes([0x42] * 32)
master, mb = find_pda([b'aspis-pair-forest-master-v1', mint], prog)
lanes = [find_pda([b'aspis-pair-forest-lane-v1', master, bytes([l])], prog) for l in range(8)]
# Cross-check against driver evidence: master 254, lane bumps, page-0/1 bumps.
print('master_bump', mb, 'lane_bumps', [b for _, b in lanes])
print('page0_bumps', [find_pda([b'aspis-pool-root-page-v1', k, struct.pack('<Q', 0)], prog)[1] for k, _ in lanes])
print('page1_bumps', [find_pda([b'aspis-pool-root-page-v1', k, struct.pack('<Q', 1)], prog)[1] for k, _ in lanes])
K = int(sys.argv[1]); maxp = int(sys.argv[2])
for page in range(maxp):
    for l, (k, _) in enumerate(lanes):
        b = find_pda([b'aspis-pool-root-page-v1', k, struct.pack('<Q', page)], prog)[1]
        if 256 - b >= K:
            print('FOUND lane', l, 'page', page, 'bump', b, 'attempts', 256 - b)
            sys.exit(0)
print('none')
