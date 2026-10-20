#!/usr/bin/env python3
"""Source-preserving qualified Variant discriminator registration."""
from pathlib import Path
import argparse,hashlib,json
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();tool=Path(__file__).resolve().parent;area=tool.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
old=b'@[discriminant isize]\ninductive transport.Variant where\n| S1 : transport.Variant\n| S2 : transport.Variant\n| D : transport.Variant\n'
new=b'''inductive transport.Variant where
| S1 : transport.Variant
| S2 : transport.Variant
| D : transport.Variant

def transport.Variant.read_discriminant : transport.Variant \xe2\x86\x92 Isize
  | .S1 => 0#isize
  | .S2 => 1#isize
  | .D => 2#isize
instance _root_.AspisR1CuQuery.transport.Variant.instDiscriminant :
    Aeneas.Std.Discriminant transport.Variant Isize where
  read_discriminant := transport.Variant.read_discriminant
'''
for name in ['Types.lean','Funs.lean']:
 raw=(tool/'cu-query-generated'/name).read_bytes();data=raw
 if name=='Types.lean':
  assert raw.count(old)==1;data=raw.replace(old,new);assert data.replace(new,old)==raw
 dest=area/'lean/AspisR1CuQuery'/name
 if a.check:assert dest.read_bytes()==data,name
 else:dest.write_bytes(data)
 print(json.dumps(dict(check=a.check,file=name,source_sha256=sha(raw),output_sha256=sha(data),change='Qualified enum-instance registration only; same constructors and ordinals.'if name=='Types.lean'else'None')))
