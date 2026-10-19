#!/usr/bin/env python3
"""Promote exact generated method slices without unused generic impl objects."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
def make(source,namespace,imports,cuts):
 raw=(here/source).read_bytes();out=b'-- Exact generated declaration cuts; bodies unchanged.\n'+imports
 assert sha(raw)=={'borrow-option-generated/Funs.lean':'a8fec72b0ca5d7e31ab68db400b390a5c1ad5137ad3de105a671abaaef7d6ac3',
  'iterator-generated/Funs.lean':'2c9f5397398a98cf028f11423b35e494f1d7f016279f6fb76022c0aa330a904d'}[source]
 out+=b'open Aeneas Aeneas.Std Result ControlFlow Error\nnamespace '+namespace.encode()+b'\n'
 pins=[]
 for start,end in cuts:
  first=raw.index(start);last=raw.index(end,first)
  out+=raw[first:last];pins.append(dict(start=first,end=last,sha256=sha(raw[first:last])))
 out+=b'end '+namespace.encode()+b'\n'
 return out,dict(source=source,source_sha256=sha(raw),cuts=pins,output_sha256=sha(out))
opt,opins=make('borrow-option-generated/Funs.lean','AspisR1CuBorrowOption',
 b'import AspisR1CuBorrowOption.Types\n',
 [(b'/-- [aspis_cu_borrow_option::{impl',b'/-- Trait implementation:'),
  (b'/-- [aspis_cu_borrow_option::from_residual]',b'end AspisR1CuBorrowOption')])
it,ipins=make('iterator-generated/Funs.lean','AspisR1CuIterator',
 b'import AspisR1CuIterator.Types\nimport AspisR1CuIterator.SourceOption\n',
 [(b'/-- [aspis_cu_iterator::{impl',b'/-- Trait implementation:')])
outputs={area/'lean/AspisR1CuBorrowOption/Operations.lean':opt,
 area/'lean/AspisR1CuIterator/Next.lean':it,
 here/'iterator-emission.json':(json.dumps(dict(option=opins,iterator=ipins,
  scope='Exact selected emitted functions; generic unused trait impl objects omitted. No emitted body changes.'),indent=2)+'\n').encode()}
for path,data in outputs.items():
 if a.check:assert path.read_bytes()==data,str(path)
 else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
print(json.dumps(dict(check=a.check,selected_functions=3)))
