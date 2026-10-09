import json,sys
P={'EAdd':112.023,'ESub':104.086,'ENeg':53.992,'EMul':1466.562,'ESquare':913.781,'EMulK':662.828,'EMulF':143.0,'EInv':2120.008,'EInvGeneric':3100.508,
'KAdd':45.0,'KSub':38.055,'KNeg':27.0,'KMul':334.414,'KSquare':214.969,'KMulF':67.0,'KMulC':143.516,'KInv':942.508,'KInvGeneric':1647.008,
'FAdd':13.0,'FSub':11.023,'FNeg':6.0,'FMul':19.008,'FInv':579.0,'FInvGeneric':1214.0,'FHalf':6.008,'FMulPow2':20.016,'ShaCompression':136.992,'ShaCall':0}
for v in ('transfer','withdrawal'):
    d=json.load(open(f'shaped-counts-{v}.json'))
    tot=0; agg={}
    for ph in d['phases']:
        name=ph['phase']; ex=ph['exclusive']
        cu=sum(P.get(k,0)*n for k,n in ex.items())
        unk=[k for k in ex if k not in P and ex[k]]
        key=name.split('(')[0]
        agg.setdefault(key,[0,0,{}]); agg[key][0]+=cu; agg[key][1]+=1
        for k,n in ex.items(): agg[key][2][k]=agg[key][2].get(k,0)+n
        tot+=cu
        if unk: print('UNPRICED',name,unk)
    print(f'== {v}: total {tot:,.0f} CU  = {tot/1.4e6:.1f} x 1.4M')
    for k,(cu,n,ex) in agg.items():
        top=sorted(((P.get(a,0)*b,a,b) for a,b in ex.items() if b),reverse=True)[:5]
        print(f'  {k:12s} n={n:2d} total {cu:12,.0f}  per {cu/n:10,.0f}  top: '+', '.join(f'{a}x{b}={c:,.0f}' for c,a,b in top))
