#!/usr/bin/env python3
"""Independent replay of the deterministic honest PF semantic evidence.

Checks C1/C2 backend lane partition, P1 framing, every scalar/circle row,
mask total, all ten sumcheck boundaries and 87 MLE/29 natural circle claims.
The backend in this fixture hashes message bytes, not encoded Merkle trees.
This is not a second PF terminal implementation or an opening acceptance test.
"""
import hashlib,json,struct
from pathlib import Path
from generate_kats import P,Q,ONE,add,neg,mul,digits,power,circle
from generate_semantic_kat import ZERO,k,sub,scale,h,enc,HERE

def decode(buf,width=32):
    d=struct.unpack('<'+'I'*(width//4),buf)
    assert all(x<P for x in d)
    if width==32: assert d[4:]==(0,)*4, 'honest fixture uses embedded K values'
    return d[:4]
def enc_k(x):return struct.pack('<4I',*x)
def mle_weights(at):
    w=[ONE]
    for x in at:
        w=[v for a in w for v in [mul(a,sub(ONE,x)),mul(a,x)]]
    return w

def main():
    proof=(HERE/'semantic-honest-pf.bin').read_bytes()
    public=(HERE/'semantic-honest-pf-public.bin').read_bytes()
    data=(HERE/'semantic-honest-pf-columns.bin').read_bytes()
    assert len(data)==29*1024*16
    cols=[[decode(data[(lane*1024+r)*16:][:16],16) for r in range(1024)] for lane in range(29)]
    assert all(x[1:]==(0,0,0) for col in cols[:26] for x in col)
    c1=h(b'\xc1'+b''.join(struct.pack('<I',x[0]) for col in cols[:26] for x in col)+b''.join(map(enc_k,cols[28])))
    c2=h(b'\xc2'+b''.join(enc_k(x) for col in cols[26:28] for x in col))
    assert proof[:32]==c1
    state=h(b'aspis:r0:20261009:v1\0'+struct.pack('<I',len(public))+public+c1)
    cursor=32; alpha=[]; rows=[]; running=None
    for row in range(27):
        tag,length=struct.unpack('<BI',proof[cursor:cursor+5]); framed=proof[cursor:cursor+5+length];payload=framed[5:];cursor+=5+length
        wanted={2:(1,32),14:(3,32),25:(4,87*32),26:(5,29*32)}.get(row,(2,28*32) if 15<=row<=24 else (0,0))
        assert (tag,length)==wanted
        if row==2:assert payload==c2
        if row==14:running=decode(payload);mask_sum=running
        if 15<=row<=24:
            poly=[decode(payload[i:i+32]) for i in range(0,length,32)]
            total=poly[0]
            for c in poly:total=add(total,c)
            assert total==running,('boundary',row)
        absorbed=h(state+bytes([0,0xa0+row])+framed); block=h(absorbed+b'\1');state=h(absorbed+b'\2')
        challenge=tuple(digits(int.from_bytes(block,'little')%Q,4))
        if 15<=row<=24:
            alpha.append(challenge);running=ZERO
            for c in reversed(poly):running=add(mul(running,challenge),c)
        if row==25:
            carry=ONE;succ=list(alpha)
            for i in range(9,-1,-1):succ[i]=sub(add(alpha[i],carry),scale(mul(alpha[i],carry),2));carry=mul(carry,alpha[i])
            xor=[sub(ONE,x) if i in [6,7] else x for i,x in enumerate(alpha)]
            claims=[decode(payload[i:i+32]) for i in range(0,length,32)]
            for point,at in enumerate([alpha,succ,xor]):
                weights=mle_weights(at)
                for lane in range(29):
                    total=ZERO
                    for w,x in zip(weights,cols[lane]):total=add(total,mul(w,x))
                    assert total==claims[29*point+lane],('claim',point,lane)
            z0=circle(list(challenge),0)
        if row==26:
            z1=circle(list(challenge),1);assert z0!=z1
            factors=[z0['x']]
            for _ in range(8):factors.append(sub(scale(mul(factors[-1],factors[-1]),2),ONE))
            weights=[]
            for r in range(1024):
                w=z0['y'] if r&1 else ONE
                for bit in range(9):
                    if (r//2)>>bit&1:w=mul(w,factors[bit])
                weights.append(w)
            for lane in range(29):
                total=ZERO
                for w,x in zip(weights,cols[lane]):total=add(total,mul(w,x))
                assert total==decode(payload[lane*32:][:32]),('circle claim',lane)
        rows.append({'row':row,'tag':tag,'payload_len':length,'block':block.hex(),'parameter':challenge,'state_after':state.hex()})
    assert cursor==len(proof)
    assert state==(HERE/'semantic-honest-pf-state.bin').read_bytes()
    exponents=[0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25,1,3,5,7,9,11,15,17,19,21]
    total=ZERO
    for r in range(1024):
        bits=[(r>>(9-i))&1 for i in range(10)]
        l0=sum((3+22*i)*bit for i,bit in enumerate(bits));l16=sum((275+150*i)*bit for i,bit in enumerate(bits))
        for lane,e in enumerate(exponents):
            basis=[0]*4;basis[(lane if lane<16 else lane-16)%4]=pow(l0,e,P)
            total=add(total,mul(cols[lane][r],basis))
        total=add(total,scale(cols[27][r],1+pow(l16,26,P)))
    assert total==mask_sum
    out={'proof_sha256':h(proof).hex(),'columns_sha256':h(data).hex(),'final_state':state.hex(),
         'checks':['C1 lanes 0..25,D before lambda','C2 H1,G only','27 P1 row hashes and blocks','mask total','10 polynomial boundaries','87 point claims including D','29 beforeZ1 natural circle values'], 'rows':rows}
    (HERE/'semantic-honest-kat.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
if __name__=='__main__':main()
