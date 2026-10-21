#!/usr/bin/env python3
"""Resolve retained Charon hash-consed type and trait implementation identities."""
import hashlib,json
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory2-20261021')
P=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020/extraction-freeze/Stage2.llbc')
raw=P.read_bytes();digest=hashlib.sha256(raw).hexdigest()
assert digest=='f11e40b4119578eee1ebef90874f436dc35b1076f6db27baaa92a79c0919538d'
x=json.loads(raw);t=x['translated'];hc={}
def walk(v):
    if isinstance(v,dict):
        if 'HashConsedValue' in v:
            i,z=v['HashConsedValue'];assert i not in hc or hc[i]==z;hc[i]=z
        for z in v.values():walk(z)
    elif isinstance(v,list):
        for z in v:walk(z)
walk(x)
def expand(v):
    if isinstance(v,dict):
        if 'Deduplicated' in v:return expand(hc[v['Deduplicated']])
        if 'HashConsedValue' in v:return expand(v['HashConsedValue'][1])
        return {k:expand(z) for k,z in v.items()}
    if isinstance(v,list):return [expand(z) for z in v]
    return v
types={r['def_id']:r for r in t['type_decls'] if r}
traits={r['def_id']:r for r in t['trait_decls'] if r}
impls={r['def_id']:r for r in t['trait_impls'] if r}
def simple(name):
    assert all('Ident' in n for n in name),name
    return '::'.join(n['Ident'][0] for n in name)
def typename(v):
    v=expand(v)
    if 'Adt' in v and 'Adt' in v['Adt']['id']:
        ty=v['Adt'];base=simple(types[ty['id']['Adt']]['item_meta']['name'])
        args=ty['generics']['types']
        return base+('<'+', '.join(typename(a) for a in args)+'>' if args else '')
    if 'Literal' in v:return json.dumps(v['Literal'],sort_keys=True)
    raise ValueError(v)
rows=[]
for f in t['fun_decls']:
    if not f:continue
    name=f['item_meta']['name'];resolved=[];impl=None
    try:
        for n in name:
            if 'Ident' in n:resolved.append(n['Ident'][0])
            elif 'Impl' in n:
                a=n['Impl']
                if 'Ty' in a:
                    impl=expand(a['Ty']);selfty=typename(impl['skip_binder']);resolved=[selfty]
                elif 'Trait' in a:
                    impl=expand(impls[a['Trait']]['impl_trait']);selfty=typename(impl['generics']['types'][0]);trait=simple(traits[impl['id']]['item_meta']['name']);resolved=['<'+selfty+' as '+trait+'>']
                else:raise ValueError(a)
            else:raise ValueError(n)
        rows.append(dict(id=f['def_id'],canonical_name='::'.join(resolved),implementation=impl))
    except (ValueError,AssertionError,KeyError) as e:
        rows.append(dict(id=f['def_id'],canonical_name=None,reason=str(e)))
out=dict(schema='s10-stage2-instance-name-resolution-v1',input=dict(path=str(P),sha256=digest,bytes=len(raw)),
    generator='tools/s10-inventory2-20261021/stage2-identities-host.py',declarations=rows,
    scope='Structural name/type resolution of retained generic LLBC; no executed instance or SBF equality inferred')
(H/'packet/stage2-identities.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(resolved=sum(r['canonical_name'] is not None for r in rows),total=len(rows))))
