#!/usr/bin/env python3
"""Independent P1 semantic transcript for a fixed, sparse 29-lane trace.

Roots are opaque fixture inputs, not an authentication claim. This tests the
semantic row schedule, sumcheck and natural-code beforeZ1 values; the separate
honest PF integration exercises the selected residual registry. No Rust output
is read. Python bigint field arithmetic comes from R-B's independent oracle.
"""
import argparse
import hashlib
import json
import struct
from pathlib import Path
from generate_kats import P, Q, ONE, add, neg, mul, digits, circle

HERE = Path(__file__).resolve().parent
ZERO = (0, 0, 0, 0)
def k(n): return (n % P, 0, 0, 0)
def sub(a,b): return add(a, neg(b))
def scale(a,n): return mul(a,k(n))
def enc(q): return struct.pack('<8I', *q, 0,0,0,0)
def h(b): return hashlib.sha256(b).digest()
def frame(row,payload):
    tag = 1 if row == 2 else 3 if row == 14 else 2 if 15 <= row <= 24 else 4 if row == 25 else 5 if row == 26 else 0
    return bytes([tag])+struct.pack('<I',len(payload))+payload

def public_bytes():
    digest = lambda n: b''.join(struct.pack('<I', n+v) for v in range(8))
    return (b'\0' + digest(10)+digest(20)+struct.pack('<I',77)+b'\1'+digest(30)
            +digest(40)+b'\0'+struct.pack('<Q',9)
            +b''.join(digest(100+8*i) for i in range(20))+digest(50)
            +b''.join(digest(300+8*i) for i in range(20)))

def trace(row):
    lo,hi=row&1,(row>>9)&1
    vals=[ZERO]*29
    vals[0]=k(7+3*lo+5*hi)
    vals[28]=add(add((11,13,17,19),scale((2,3,5,7),lo)),scale((23,29,31,37),hi))
    return vals

def claims(at):
    out=[ZERO]*29
    out[0]=add(k(7),add(scale(at[9],3),scale(at[0],5)))
    out[28]=add((11,13,17,19),add(mul((2,3,5,7),at[9]),mul((23,29,31,37),at[0])))
    return out

def endpoints(z):
    factors=[z['x']]
    for _ in range(8): factors.append(sub(scale(mul(factors[-1],factors[-1]),2),ONE))
    out=[ZERO]*29
    for r in range(1024):
        weight = z['y'] if r&1 else ONE
        for bit in range(9):
            if (r//2)>>bit&1: weight=mul(weight,factors[bit])
        vals=trace(r)
        for lane in [0,28]: out[lane]=add(out[lane],mul(weight,vals[lane]))
    return out

def generate():
    public=public_bytes()
    c1=h(b'R0 semantic fixture C1 root'); c2=h(b'R0 semantic fixture C2 root')
    state=h(b'aspis:r0:20261009:v1\0'+struct.pack('<I',len(public))+public+c1)
    iv=state; proof=bytearray(c1); states=bytearray(); challenges=bytearray(); rows=[]; alpha=[]
    for row in range(27):
        payload=b''
        if row==2: payload=c2
        elif row==14: payload=enc(k(11264))
        elif 15<=row<=24:
            r=row-15; coeff=[ZERO]*28
            if r==0:
                coeff[0]=k(512*7+256*3); coeff[1]=k(512*5)
            elif r<9:
                coeff[0]=scale(add(k(7),add(scale(alpha[0],5),k(3*pow(2,-1,P)))),2**(9-r))
            else:
                coeff[0]=add(k(7),scale(alpha[0],5)); coeff[1]=k(3)
            payload=b''.join(map(enc,coeff))
        elif row==25:
            carry=ONE; successor=list(alpha)
            for i in range(9,-1,-1):
                successor[i]=sub(add(alpha[i],carry),scale(mul(alpha[i],carry),2)); carry=mul(carry,alpha[i])
            xor=[sub(ONE,a) if i in [6,7] else a for i,a in enumerate(alpha)]
            point_claims=[claims(at) for at in [alpha,successor,xor]]
            payload=b''.join(enc(x) for c in point_claims for x in c)
        elif row==26: payload=b''.join(map(enc,endpoints(z0)))
        record=frame(row,payload); before=state
        absorbed=h(state+bytes([0,0xa0+row])+record)
        block=h(absorbed+b'\1'); state=h(absorbed+b'\2')
        sample=digits(int.from_bytes(block,'little')%Q,4)
        if row<25:
            challenges.extend(struct.pack('<4I',*sample))
            if row>=15: alpha.append(tuple(sample))
        else:
            z=circle(sample,row-25)
            challenges.extend(struct.pack('<8I',*z['x'],*z['y']))
            if row==25: z0=z
        proof.extend(record); states.extend(state)
        rows.append({'row':row,'label':hex(0xa0+row),'tag':record[0],'payload_len':len(payload),
                     'state_before':before.hex(),'absorbed':absorbed.hex(),'block':block.hex(),
                     'state_after':state.hex(),'parameter':sample})
    data={'description':__doc__,'trace':'lane0=7+3*bit0+5*bit9; lane28=[11,13,17,19]+bit0*[2,3,5,7]+bit9*[23,29,31,37]; other lanes zero',
          'iv':iv.hex(),'public_bytes':public.hex(),'c1_root':c1.hex(),'c2_root':c2.hex(),
          'proof_sha256':h(proof).hex(),'rows':rows}
    return {'semantic-kat.json':(json.dumps(data,indent=2)+'\n').encode(),
            'semantic-kat.bin':bytes(proof),'semantic-kat-public.bin':public,
            'semantic-kat-states.bin':bytes(states),'semantic-kat-challenges.bin':bytes(challenges)}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--check',action='store_true'); args=parser.parse_args()
    for name,data in generate().items():
        path=HERE/name
        if args.check:
            assert path.read_bytes()==data, name
        else: path.write_bytes(data)
        print(name, len(data), h(data).hex())
if __name__=='__main__': main()
