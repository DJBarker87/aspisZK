#!/usr/bin/env python3
"""Resolve static trait-implementation calls in existing verifier extractions."""
import collections,hashlib,json,sys
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory2-20261021')
F=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory-20261021')
sha=lambda b:hashlib.sha256(b).hexdigest()
name=sys.argv[1];p=F/name/'Program.llbc';raw=p.read_bytes();input_pin=dict(path=str(p),sha256=sha(raw),bytes=len(raw))
x=json.loads(raw);del raw;t=x['translated'];hc={}
def walk(v):
    if isinstance(v,dict):
        yield v
        if 'HashConsedValue' in v:
            i,z=v['HashConsedValue'];assert i not in hc or hc[i]==z;hc[i]=z
        for z in v.values():yield from walk(z)
    elif isinstance(v,list):
        for z in v:yield from walk(z)
for _ in walk(x):pass
def expand(v):
    if isinstance(v,dict):
        if 'Deduplicated' in v:return expand(hc[v['Deduplicated']])
        if 'HashConsedValue' in v:return expand(v['HashConsedValue'][1])
        return {k:expand(z) for k,z in v.items()}
    if isinstance(v,list):return [expand(z) for z in v]
    return v
impls={r['def_id']:r for r in t['trait_impls'] if r};funs={r['def_id']:r for r in t['fun_decls'] if r}
result=[]
for f in funs.values():
    index=0
    for v in walk(f['body']):
        if 'Call' not in v:continue
        func=expand(v['Call']['call']['func']);kind=func.get('Regular',{}).get('kind',{})
        current=index;index+=1
        if 'Fun' in kind:continue
        row=dict(caller=f['def_id'],call_index=current,function_sha256=sha(json.dumps(func,sort_keys=True,separators=(',',':')).encode()),target=None)
        if 'Trait' in kind:
            ref,method=kind['Trait'];k=ref['kind'];row.update(trait_kind=next(iter(k)),method_index=method,trait_ref_sha256=sha(json.dumps(ref,sort_keys=True).encode()))
            if 'TraitImpl' in k:
                impl=k['TraitImpl'];methods=impls[impl['id']]['methods']
                trait_id=ref['trait_decl_ref']['skip_binder']['id']
                selected=[m for m in methods if m['kind'].get('TraitMethod')==[trait_id,method]]
                assert len(selected)<=1,(trait_id,method)
                if selected:
                    target=selected[0]['skip_binder']['id']
                    assert target in funs,(name,f['def_id'],target)
                    row.update(target=target,impl_id=impl['id'],method_reference=expand(selected[0]),status='static LLBC trait-implementation method; independent corroboration required')
                else:
                    row.update(status='implementation has no emitted method reference for this trait item; no edge invented',
                        impl_id=impl['id'],requested_trait_id=trait_id,implemented_trait_id=impls[impl['id']]['impl_trait']['id'],
                        emitted_method_keys=[m['kind'] for m in methods])
            else:row['status']='generic trait clause or other unresolved trait target'
        else:row.update(trait_kind='Dynamic',status='dynamic MIR operand; pointer-flow required')
        result.append(row)
out=dict(schema='s10-retained-trait-edge-resolution-v1',input=input_pin,graph=name+'.json',generator='tools/s10-inventory2-20261021/trait-edges-host.py',
    calls=result,counts=dict(total=len(result),static=sum(r['target'] is not None for r in result),kinds=dict(collections.Counter(r['trait_kind'] for r in result))))
raw=(json.dumps(out,indent=2,sort_keys=True)+'\n').encode();assert len(raw)<=5_000_000
(H/'packet'/f'trait-edges-{name}.json').write_bytes(raw);print(json.dumps(out['counts']))
