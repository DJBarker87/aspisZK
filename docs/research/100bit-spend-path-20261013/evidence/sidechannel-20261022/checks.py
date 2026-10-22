#!/usr/bin/env python3
"""Tiny exact source-expression examples; NOT a Kani or compiled-code proof."""
from fractions import Fraction
from pathlib import Path
import hashlib, json, subprocess, time
E=Path(__file__).resolve().parent
R=E.parents[4]
P=2**31-1
start=time.monotonic()
checks=[]
def record(name, source, examples, limit):
    checks.append(dict(name=name, source=source, examples=examples, limitation=limit))

def add(a,b):
    s=a+b
    return dict(branch=s>=P, value=s-P if s>=P else s)
assert add(0,1)['branch'] != add(P-1,1)['branch']
record('canonical add two-run counterexample','crates/aspis-core/src/field.rs:88',
       [dict(a=a,b=1,**add(a,1)) for a in (0,P-1)],'Source expression evaluated in Python, not an instrumented native trace; helper inputs canonical, not a same-public full-spend witness pair.')

def red(x):
    x=(x&P)+(x>>31); x=(x&P)+(x>>31)
    return dict(branch=x>=P,value=x-P if x>=P else x)
assert red(0)['branch'] != red(P)['branch']
assert red((P-1)*(P-1))['value']==1
record('Mersenne reduction branch','crates/aspis-core/src/field.rs:40',
       [dict(input=x,**red(x)) for x in (0,P,(P-1)*(P-1))], 'Input P can arise as a lazy sum; product-specific reachability is not asserted for P.')
record('canonical negation','crates/aspis-core/src/field.rs:125',
       [dict(x=x,branch=x==0,value=0 if x==0 else P-x) for x in (0,1)],'Canonical helper values; direct source counterexample.')

def sample(words):
    for i,w in enumerate(words[:16]):
        c=w&0x7fffffff
        if c<P: return dict(draws=i+1,candidate=c,exhausted=False)
    return dict(draws=16,exhausted=True)
assert sample([0])['draws']==1
assert sample([P,0])['draws']==2
assert sample([P]*16)['exhausted']
record('limb rejection count','crates/aspis-prover/src/state_only_hiding.rs:361; state_only_entropy.rs:794',
       [sample(x) for x in ([0],[P,0],[P]*16)],'Explicit word streams; finding depends on private coins, independently of witness. Does not find a SHA256 seed realizing a chosen stream.')
# Concrete gamma wrap: the deployed base-P arithmetic tests carry beyond digit 7.
def gamma_wrap(rank):
    low=rank%(P**8); high=rank//(P**8)
    return low+high+1>=P**8
assert not gamma_wrap(0) and gamma_wrap(P**8-1)
record('gamma wrapped branch','crates/aspis-r1-cost-probe/src/sampler.rs:115',
       [dict(rank=str(x),wrapped=gamma_wrap(x)) for x in (0,P**8-1)],'Actual 256-bit input ranks, both representable. Fixed rank test, not a ROM probability claim.')
# Nonzero 64-byte draws under E1, two independent 32-byte blocks.
s=(1-Fraction(1,2**256))**2
f=1-s
assert sum(f**(n-1)*s for n in range(1,17))+f**16==1
record('64-byte entropy exact capped geometric normalization','crates/aspis-prover/src/state_only_entropy.rs:202',
       dict(success_per_draw='(1-2^-256)^2', success_at_n='(1-(1-2^-256)^2)^(n-1)*(1-2^-256)^2, 1<=n<=16', zero_exhaustion='(1-(1-2^-256)^2)^16'), 'Conditional on every RNG call succeeding with independent uniform bytes; arbitrary environment failures stop this distribution.')
# Eight-attempt normalization, including abort hazards; rational test values only.
r,a,e=Fraction(1,3),Fraction(1,2),Fraction(1,6)
assert sum(r**k*(a+e) for k in range(8))+r**8==1
record('retry hazard normalization','crates/aspis-r1-cost-probe/src/prover.rs:354',
       dict(reject='1/3',success='1/2',abort='1/6', mass='sum_{k=0}^7 r^k(a+e)+r^8 = 1'), 'Toy rational hazards verify the formula only; these are not measured or proved R1 probabilities.')
# A local compression example with two tagged tuples, embedded in M31 subset of K.
# tag + lambda * first_limb: equal compressed values vs distinct values.
sets=[{1,2},{1,(2+(P-1))%P}]
assert [len(x) for x in sets]==[2,1]
record('pole-set cardinality can depend on tuple limbs','crates/aspis-statement/src/logup.rs:75; crates/aspis-r1-cost-probe/src/host_semantic.rs:273',
       [dict(lambda_value=1,tags=[1,2],first_limbs=[0,x],pole_set=sorted(y),cardinality=len(y)) for x,y in zip((0,P-1),sets)], 'Local two-tuple obstruction only. Not instantiated to the fixed forest registry or a same-public valid-spend witness pair; does not prove an exploitable deployed count gap.')
# QueryScan abstracts precisely the duplicate test; successful trace differs with same ordered output.
def scan(words):
    out=[];comparisons=[]
    for w in words:
        if len(out)==22: break
        comparisons.append(w in out)
        if w not in out: out.append(w)
    return dict(draws=len(comparisons),duplicate_branches=comparisons,queries=out)
x=scan(list(range(22)));y=scan([0,0]+list(range(1,22)))
assert x['queries']==y['queries'] and x['draws']!=y['draws']
record('same query list does not determine duplicate trace','crates/aspis-core/src/r0_transcript.rs:202', [x,y], 'Candidate words model the scan; no SHA256 preimage asserted. Early stop-before-next-word and selected advance are covered by source, not this simplified output model.')
result=dict(kind='tiny exact source-expression/model checks',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),exit=0,wall_seconds=time.monotonic()-start, checks=checks, kani='not run',lean='not run',compiled_or_hardware_measurements='none')
(E/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(checks=len(checks),exit=0,wall_seconds=result['wall_seconds'])))
