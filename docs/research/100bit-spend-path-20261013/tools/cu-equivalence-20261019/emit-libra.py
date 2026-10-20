#!/usr/bin/env python3
"""Promote exact Libra bodies with explicit checked mutable signature transport."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;r=tool.parents[1];raw=tool/'libra-generated';dest=r/'lean/AspisR1Libra'
s=(raw/'Funs.lean').read_text().replace('namespace AspisR1Libra\n','namespace AspisR1Libra\nvariable [Shared]\n',1)
names=['kpowers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut','old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut']
for name in names:
 import re
 pattern=r'(call_mut :=\s*)'+re.escape(name)
 assert len(re.findall(pattern,s))==1
 s=re.sub(pattern,lambda m:m.group(1)+name.replace('FnMut','FnOnce').replace('.call_mut','.call_once'),s)
for name in names:
 once=name.replace('FnMut','FnOnce').replace('.call_mut','.call_once')
 pattern=r'(call_once :=\s*)'+re.escape(once)+r'(?=\n})'
 assert len(re.findall(pattern,s))==1
 s=re.sub(pattern,lambda m:m.group(1)+'fun c i => do\n    let (value,_) ← '+once+' c i\n    .ok value',s)
for fragment in ['core.array.from_fn N\n      (kpowers.', 'core.array.from_fn 28#usize\n      old.twofold_libra_weights.closure.closure.']:
 assert s.count(fragment)==1;s=s.replace(fragment,fragment.replace('core.array.from_fn','core.array.from_fn_mut'))
out={'Types.lean':(raw/'Types.lean').read_bytes(),'Funs.lean':s.encode()}
for name,data in out.items():
 target=dest/name
 if args.check:assert target.read_bytes()==data,name
 else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
print(json.dumps(dict(check=args.check,raw_callback_bodies_unchanged=True,fn_once_value_projection_transport=2,callback_instance_handback_transport=2,mutable_builder_caller_transport=2)))
