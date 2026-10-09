"""Independent diagnostic transcriptions, NOT Lean or SBF execution.
Audit target: DJBarker87/aspisZK @ 30a303a344dbb42e24ad8f42a8804819747942bc.
Compare Rust's imperative Merkle loop with Lean's functional loop using SHA-256.
Also exercise the byte-boundary gap in the current composed theorem.
"""
from __future__ import annotations
import hashlib, itertools, json, math, random
from fractions import Fraction
from pathlib import Path

D = 26
P = 2**31 - 1
ROOT_START, NONCE_START, RECORD_START, FRONTIER_START = 11152,11204,11228,24890

def h(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()[:D]

def seed(s: str) -> tuple[bytes, bytes]:
    return h((s+'/0').encode()), h((s+'/1').encode())

def parent(pos, cur, sib):
    l,r = (cur,sib) if pos%2==0 else (sib,cur)
    calls = (b'\x11'+l[0]+r[0], b'\x11'+l[1]+r[1])
    return (pos//2, h(calls[0]),h(calls[1])),calls

def guards(depth, entries, left, right):
    return bool(entries) and 0<=depth<32 and len(left)%D==len(right)%D==0 and len(left)==len(right) and all(a[0]<b[0] for a,b in zip(entries,entries[1:])) and entries[-1][0]<2**depth

def imperative(depth, entries, left, right, roots):
    if not guards(depth,entries,left,right): return None
    level=list(entries); node_pos=0; trace=[]
    for _ in range(depth):
        nxt=[]; i=0
        while i<len(level):
            pos,c1,c2=level[i]
            if pos%2==0 and i+1<len(level) and level[i+1][0]==pos+1:
                sibling=level[i+1][1:]; i+=2
            else:
                if node_pos+D>len(left): return None
                sibling=(left[node_pos:node_pos+D],right[node_pos:node_pos+D]); node_pos+=D; i+=1
            ent,calls=parent(pos,(c1,c2),sibling); nxt.append(ent);trace.extend(calls)
        level=nxt
    return tuple(trace) if node_pos==len(left) and level==[(0,*roots)] else None

def functional(depth, entries, left, right, roots):
    if not guards(depth,entries,left,right): return None
    frontier=tuple((left[i:i+D],right[i:i+D]) for i in range(0,len(left),D))
    def run_pass(fuel, entries, fr):
        if not entries: return (),fr,()
        if fuel==0:return None
        pos,c1,c2=entries[0]
        if pos%2==0 and len(entries)>1 and entries[1][0]==pos+1:
            sibling=entries[1][1:]; tail=run_pass(fuel-1,entries[2:],fr)
        else:
            if not fr:return None
            sibling=fr[0];tail=run_pass(fuel-1,entries[1:],fr[1:])
        if tail is None:return None
        ent,calls=parent(pos,(c1,c2),sibling)
        out,remaining,trace=tail
        return (ent,)+out,remaining,calls+trace
    def levels(n,entries,fr):
        if n==0:return entries,fr,()
        first=run_pass(len(entries),entries,fr)
        if first is None:return None
        out,remain,tr=first
        later=levels(n-1,out,remain)
        if later is None:return None
        final,remaining,trace=later
        return final,remaining,tr+trace
    result=levels(depth,tuple(entries),frontier)
    if result is None:return None
    final,remaining,trace=result
    return trace if final==((0,*roots),) and remaining==() else None

def fixture(depth, positions):
    entries=[(i,*seed('leaf/'+str(i))) for i in sorted(positions)]
    level=entries; frontier=[]
    for lev in range(depth):
        nxt=[];i=0
        while i<len(level):
            pos,c1,c2=level[i]
            if pos%2==0 and i+1<len(level) and level[i+1][0]==pos+1:
                sibling=level[i+1][1:];i+=2
            else:
                sibling=seed(f'frontier/{lev}/{pos^1}');frontier.append(sibling);i+=1
            ent,_=parent(pos,(c1,c2),sibling);nxt.append(ent)
        level=nxt
    assert len(level)==1
    left=b''.join(x[0] for x in frontier);right=b''.join(x[1] for x in frontier)
    return entries,left,right,level[0][1:]

def wire_parse(body):
    if len(body)<FRONTIER_START or len(body)>40282 or (len(body)-FRONTIER_START)%52:return None
    limbs=[int.from_bytes(body[i:i+4],'little') for i in range(0,ROOT_START,4)]
    if any(x>=P for x in limbs):return None
    half=(len(body)-FRONTIER_START)//2
    return dict(values=tuple(limbs), roots=(body[11152:11178],body[11178:11204]), nonces=body[11204:11228],records=body[11228:24890],frontiers=(body[24890:24890+half],body[24890+half:]))

def main():
    rng=random.Random(20260911);passed=0;valid=0;mutations=0
    def test(depth,entries,left,right,roots,expected=None):
        nonlocal passed,valid,mutations
        a=imperative(depth,entries,left,right,roots);b=functional(depth,entries,left,right,roots)
        assert a==b
        if expected is not None:assert (a is not None)==expected
        passed+=1
        if a is not None:valid+=1
    for depth in range(4):
        for mask in range(1,1<<(1<<depth)):
            entries,left,right,roots=fixture(depth,[i for i in range(1<<depth) if mask>>i&1])
            test(depth,entries,left,right,roots,True)
    for _ in range(2000):
        depth=rng.randrange(1,19);q=rng.randrange(1,min(32,1<<depth)+1)
        entries,left,right,roots=fixture(depth,rng.sample(range(1<<depth),q))
        test(depth,entries,left,right,roots,True)
        bads=[(depth,entries,left,right,(h(b'wrong-root'),roots[1])),
              (depth,entries,left+b'\0',right+b'\0',roots),
              (depth,entries,left+bytes(D),right+bytes(D),roots),
              (depth,[],left,right,roots),
              (32,entries,left,right,roots)]
        if len(entries)>1:bads.extend([(depth,entries[::-1],left,right,roots),(depth,[entries[0]]+entries,left,right,roots)])
        if left:bads.append((depth,entries,left[:-D],right[:-D],roots))
        for case in bads:test(*case,False);mutations+=1
    # A maximum-frontier q22/depth18 fixture: all 16 level4 prefixes, 22 distinct level5 prefixes.
    prefixes=list(range(0,32,2))+list(range(1,12,2))
    positions=[i<<13 for i in prefixes]
    entries,left,right,roots=fixture(18,positions)
    assert len(left)//D==296
    test(18,entries,left,right,roots,True)
    # Demonstrate wire fixed-fields can change while all Merkle-visible projections are identical.
    body=bytearray(40282)
    body[11152:11178]=roots[0];body[11178:11204]=roots[1]
    body[24890:24890+len(left)]=left;body[24890+len(left):]=right
    original=wire_parse(bytes(body));body[0]=1;changed=wire_parse(bytes(body))
    assert original and changed and original['values']!=changed['values']
    for k in ['roots','nonces','records','frontiers']:assert original[k]==changed[k]
    # The zero packed records in this parser demonstration are not claimed to authenticate.
    # The source theorem's separation of Program fields from Wire values is a signature finding,
    # not a full cryptographic or runtime counterexample.
    K=P**4;N=K-P**2
    pair=Fraction(90407376*90407375,N*(N-1))
    result={'target':'30a303a344dbb42e24ad8f42a8804819747942bc','test_type':'independent Python transcriptions; NOT Lean/SBF execution',
            'merkle_comparisons':passed,'accepted_fixtures':valid,'negative_mutations':mutations,
            'mismatches':0,'max_frontier_q22_depth18':296,
            'wire_fixed_field_mutation_preserves_merkle_projections':True,
            'max_body_bytes':697*16+52+24+22*621+52*296,
            'combined_pair_root_bits':math.log2(pair.denominator)-math.log2(pair.numerator),
            'pair_root_note':'Arithmetic check only, not actual-ROM sampler proof.'}
    Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
