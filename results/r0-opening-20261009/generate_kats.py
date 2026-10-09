#!/usr/bin/env python3
"""Extend the independent R-B/R-C oracles with adopted P1 rows 0–31.

No Rust arithmetic is invoked/read. D13's inventory KAT supplies the fixed
pad rows; this oracle reconstructs π independently. Includes c4 and every
returned state. Synthetic canonical semantic records test transcript plumbing,
not the payment semantic relation. Full-size authentic proofs are Rust tests.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
f = load('codes', HERE.parent / 'r0-codes-20261009/generate_kats.py')
b = load('samplers', HERE.parent / 'r0-samplers-20261009/generate_kats.py')
def value(seed, index): return tuple((seed+(index+1)*(h+3)+17*h*h) % f.P for h in range(8))
def values(seed, n): return [value(seed, j) for j in range(n)]
def encode(xs): return b''.join(v.to_bytes(4,'little') for x in xs for v in x)
def dot(a,c):
    out=f.ZERO
    for x,y in zip(a,c): out=f.add(out,f.mul(x,y))
    return out
MASKS = [6144,6144,6145,6145,6145,6145,6145,6145,
6145,6145,6145,6145,6145,6145,6145,6145,
6145,6145,6145,6145,6145,6145,6145,6145,
6145,6144,4097,2048,6145,2049,2048,6145,
2049,6145,6145,6145,6145,6145,6145,6145,
6145,6145,6145,6145,6145,6145,6145,6145,
6145,6145,6145,6145,6145,4097,6145,6145,
4097,26214,26214,26214,26214,26214,26214,1749]
def points(alphas):
    p0=list(reversed(alphas)); carry=f.ONE; p1=[]
    for x in p0:
        p1.append(f.sub(f.add(x,carry),f.scale(f.mul(x,carry),2)))
        carry=f.mul(carry,x)
    return [p0,p1,[f.sub(f.ONE,x) if j in (2,3) else x for j,x in enumerate(p0)]]
def eq(p,r):
    out=f.ONE
    for j,x in enumerate(p): out=f.mul(out,x if (r>>j)&1 else f.sub(f.ONE,x))
    return out
def build():
    inventory = json.loads((HERE / 'transport-kat.json').read_text())
    pads = inventory['pads']
    assert len(pads) == len(set(pads)) == 89
    order = pads + [r for r in range(1023) if r not in pads] + [1023]
    pi = [0] * 1024
    for j, r in enumerate(order): pi[r] = j
    assert pi == inventory['pi'] and order == inventory['inverse']
    assert hashlib.sha256(b''.join(j.to_bytes(2, 'little') for j in pi)).hexdigest() == inventory['sha256']
    # Valid all-zero privateTransfer public data per P1: variant, 3 digests,
    # assetId, two None options, u64 index, frontier/root/frontier.
    public=bytes(1+32+32+4+1+32+1+8+640+32+640)
    c1=bytes(range(32)); c2=bytes(reversed(range(32)))
    state=hashlib.sha256(b'aspis:r0:20261009:v1\0'+len(public).to_bytes(4,'little')+public+c1).digest()
    rows=[]; challenges=[]; z=[]; claim_prime=None; weights=None; kappa=gamma=None
    claims=values(101,87); y0=values(211,29); y=values(307,58); v=value(401,0)
    sent=values(503,6); final=values(601,256); polynomial=None
    for row in range(32):
        if row in [0,1] or 3<=row<=13: tag,payload=0,b''
        elif row==2: tag,payload=1,c2
        elif row==14: tag,payload=3,encode([value(14,0)])
        elif 15<=row<=24: tag,payload=2,encode(values(row,28))
        elif row==25: tag,payload=4,encode(claims)
        elif row==26: tag,payload=5,encode(y0)
        elif row==27: tag,payload=6,encode(y)
        elif row==28: tag,payload=7,encode([v])
        elif row==29: tag,payload=8,b''
        elif row==30:
            ps=points(challenges[15:25]); kp=[f.power(kappa,j) for j in range(1,4)]
            gp=[f.power(gamma,l) for l in range(29)]
            weights=[]
            for r in order: # coefficient j has semantic row π⁻¹(j)
                base=f.ZERO if (MASKS[r//16]>>(r%16))&1 else f.ONE
                weights.append(f.add(base,dot(kp,[eq(p,r) for p in ps])))
            claim=f.add(v,dot(kp,[dot(gp,claims[29*j:29*j+29]) for j in range(3)]))
            iy=f.interpolation(z[0],z[1],[dot(gp,y[j::2]) for j in range(2)])
            claim_prime=f.sub(claim,dot(weights,iy))
            c4=f.sub(f.scale(claim_prime,pow(4,f.P-2,f.P)),sent[0])
            polynomial=sent[:4]+[c4]+sent[4:]
            tag,payload=9,encode(polynomial)
        else: tag,payload=10,encode(final)
        framed=bytes([tag])+len(payload).to_bytes(4,'little')+payload
        absorbed=hashlib.sha256(state+bytes([0,0xa0+row])+framed).digest()
        if row==31:
            blocks=[]; advances=[]; state=absorbed
            for _ in range(8):
                blocks.append(hashlib.sha256(state+b'\1').digest())
                state=hashlib.sha256(state+b'\2').digest();advances.append(state)
            scanned=b.scan(blocks); state=advances[scanned['blocks']-1]
            result=scanned['accepted']
        else:
            block=hashlib.sha256(absorbed+b'\1').digest()
            state=hashlib.sha256(absorbed+b'\2').digest()
            rank=int.from_bytes(block,'little')
            if row<25:
                result=b.digits(rank % b.Q,4)+[0]*4;challenges.append(tuple(result))
            elif row<27:
                zz=b.circle(b.digits(rank%b.Q,4),row-25)
                result=[list(zz['x'])+[0]*4,list(zz['y'])+[0]*4];z.append(tuple(map(tuple,result)))
            elif row==27: result=b.digits(rank%(b.E-1)+1,8);gamma=tuple(result)
            else:
                result=b.digits(rank%b.E,8)
                if row==28:kappa=tuple(result)
        rows.append(dict(row=row,tag=tag,label=0xa0+row,payload_sha256=hashlib.sha256(payload).hexdigest(),
            absorb=absorbed.hex(),state=state.hex(),result=result))
    # Independent SHA-256 path grammar KAT: one complete 6-level path, all
    # sibling slots populated distinctly, fixed canonical zero-valued leaf.
    index=12345; current=hashlib.sha256(bytes([0x10,0x71])+bytes(480)).digest()
    siblings=[]
    for depth in range(6):
        row=[hashlib.sha256(bytes([depth,j])).digest() for j in range(7)]
        siblings.append([x.hex() for x in row]);slot=index%8
        children=row[:slot]+[current]+row[slot:]
        current=hashlib.sha256(b'\x18'+b''.join(children)).digest();index//=8
    return dict(profile='P1, full SHA-256 roots, seven absorbed coefficients',rows=rows,
        claim_prime=claim_prime,polynomial=polynomial,
        weights_sha256=hashlib.sha256(encode(weights)).hexdigest(),
        points=points(challenges[15:25]),merkle=dict(index=12345,root=current.hex(),siblings=siblings))
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    text=json.dumps(build(),indent=2)+'\n';path=HERE/'kats.json'
    if args.check:
        if path.read_text()!=text:raise SystemExit('independent opening KAT mismatch')
        print('P1 opening/transcript/path KATs reproduce exactly')
    else:path.write_text(text);print('wrote kats.json')
if __name__=='__main__':main()
