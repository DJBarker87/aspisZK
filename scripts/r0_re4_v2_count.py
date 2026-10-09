#!/usr/bin/env python3
"""Pre-implementation V2 cost ledger. No verifier arithmetic is executed.

Counts field calls and explicit vector element accesses, not compiler output.
The chosen forward map is the literal transpose of the sparse column reader.
"""
import hashlib, json, re
from pathlib import Path
root=Path(__file__).resolve().parent.parent
out=root/'results/r0-e2e-20261009/re4'
# Enumerate the exact bit-carry shape; column 511 has 256 nonzero overflow terms.
coeffs=[int(x) for x in re.search(r'= \[([^]]+)\]',(root/'crates/aspis-core/src/r0/top_overflow.rs').read_text(),re.S).group(1).split(',') if x.strip()]
nz=sum(x!=0 for x in coeffs)
occupied=clear=0
for j in range(512):
    bit=1
    while bit<512 and j&bit: occupied+=1;bit*=2
    clear+=bit<512
terms=occupied+clear+nz
assert (occupied,clear,nz,terms)==(511,511,256,1278)
# Includes the overflow result's one final factor multiply, per X map.
xmul=terms+1
masks=[int(x) for x in re.search(r'COPY_ACTIVE_ROW_MASKS: \[u16; 64\] = \[([^]]+)\]',(root/'crates/aspis-core/src/r0/opening.rs').read_text(),re.S).group(1).split(',') if x.strip()]
inactive=1024-sum(x.bit_count() for x in masks)
assert inactive==810
# Full V2, including line construction, c(alpha), powers (4 calls), tau²,
# top-row recurrences and final quarter. No dead-code elimination assumed.
a=dict(EMul=1039,EMulK=6146,EMulF=3*xmul+1,KMul=3069,KMulF=2,EAdd=9991,ESub=515,KAdd=0,KSub=3069,KNeg=1,FMul=3*511+35,FAdd=18)
b=dict(EMul=788,EMulK=4098,EMulF=1,KMul=3069+4*3072,KMulF=4*3*xmul+2,EAdd=4109,ESub=3,KAdd=4*(3*xmul+2048),KSub=3069+4*512,KNeg=1,FMul=4*3*511+35,FAdd=18)
c=dict(EMul=788,EMulK=6146,EMulF=3*xmul+1,KMul=3069,KMulF=2,EAdd=3*terms+2048+3072+inactive+13,ESub=515,KAdd=0,KSub=3069,KNeg=1,FMul=3*511+35,FAdd=18)
b_dense=dict(b,EMulK=6144,EMulF=0,EAdd=6156)
# Element accesses: includes fallible zero initialization, tensor reads/writes,
# explicit gathers/scatters and final coefficients; excludes scalar temporaries,
# stack, canonical byte decoding, and read-only coefficient/index table loads.
mem={
 'current':dict(E_reads=11261,E_writes=9731,K_reads=6141,K_writes=7162),
 'scalars_outside_sparse_images':dict(E_reads=4355,E_writes=2048,K_reads=37861,K_writes=26106),
 'scalars_outside_six_dense_dots':dict(E_reads=6400,E_writes=2048,K_reads=39909,K_writes=28157),
 'transpose_onto_F':dict(E_reads=12583,E_writes=10490,K_reads=6141,K_writes=7162),
}
prices={x['primitive']:x['cu_per_op'] for x in json.loads((root/'results/r0-e2e-20261009/re2/primitive-costs.json').read_text())['records'] if x['n']==128}
primitive=out/'s3-primitive-costs.json'
if primitive.exists(): prices.update({x['primitive']:x['cu_per_op'] for x in json.loads(primitive.read_text())['records'] if x['n']==128})
else: raise RuntimeError('Karatsuba calibration required before pricing')
records=[]
for name,ops in [('current',a),('scalars_outside_six_dense_dots',b_dense),('scalars_outside_sparse_images',b),('transpose_onto_F',c)]:
    prod=27*ops['EMul']+18*ops['EMulK']+8*ops['EMulF']+9*ops['KMul']+4*ops['KMulF']+ops['FMul']
    norm=4*ops['EMulK']+ops['EMulF']
    add=93*ops['EMul']+46*ops['EMulK']+23*ops['KMul']+8*(ops['EAdd']+ops['ESub'])+4*(ops['KAdd']+ops['KSub'])+ops['FAdd']
    traffic=32*(mem[name]['E_reads']+mem[name]['E_writes'])+16*(mem[name]['K_reads']+mem[name]['K_writes'])
    records.append(dict(order=name,operations=ops,mul_reductions=prod,operand_mod_P_normalizations=norm,canonical_add_sub_reductions=add,vector_accesses=mem[name],vector_bytes=traffic,arithmetic_estimate_cu=sum(prices[k]*v for k,v in ops.items())))
record={'status':'pre-implementation static counts, arithmetic estimate only; memory traffic not CU-priced','current_onchain_sha256':hashlib.sha256((root/'crates/aspis-core/src/r0/onchain.rs').read_bytes()).hexdigest(),'x_map':{'occupied':occupied,'clear':clear,'overflow_nonzero':nz,'products':xmul,'transpose_adds':xmul,'forward_adds':terms},'counts':records,'selected':min(records,key=lambda r:r['arithmetic_estimate_cu'])['order'],'prices':prices}
(out/'v2-order-counts.json').write_text(json.dumps(record,indent=2)+'\n')
for r in records: print(r['order'],r['operations'],'reductions',r['mul_reductions'],r['operand_mod_P_normalizations'],r['canonical_add_sub_reductions'],'vector bytes',r['vector_bytes'],'CU estimate',round(r['arithmetic_estimate_cu']))
print('SELECTED',record['selected'])
