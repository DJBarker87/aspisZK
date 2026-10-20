#!/usr/bin/env python3
"""Source-preserving mutable closure signature transport, like checked Libra."""
from pathlib import Path
import re,argparse,json
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];raw=tool/'canonical-inputs-generated';dest=area/'lean/AspisR1CanonicalInputs'
s=(raw/'Funs.lean').read_text();name='weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut';once=name.replace('FnMut','FnOnce').replace('.call_mut','.call_once')
pattern=r'(call_mut :=\s*)'+re.escape(name);assert len(re.findall(pattern,s))==1;s=re.sub(pattern,lambda m:m.group(1)+once,s)
pattern=r'(call_once :=\s*)'+re.escape(once)+r'(?=\n})';assert len(re.findall(pattern,s))==1;s=re.sub(pattern,lambda m:m.group(1)+'fun c i => do\n    let (value,_) ← '+once+' c i\n    .ok value',s)
f='core.array.from_fn N\n      (weights.powers.';assert s.count(f)==1;s=s.replace(f,f.replace('core.array.from_fn','core.array.from_fn_mut'))
for n,b in {'Types.lean':(raw/'Types.lean').read_bytes(),'Funs.lean':s.encode()}.items():
 target=dest/n
 if a.check:assert target.read_bytes()==b,n
 else:target.parent.mkdir(exist_ok=True);target.write_bytes(b)
print(json.dumps(dict(check=a.check,callback_transport=1,mutable_builder_transport=1,raw_callback_bodies_unchanged=True)))
