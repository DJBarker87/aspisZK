#!/usr/bin/env python3
"""Share only byte-identical emitted carriers/constants; retain all caller bodies."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1]
def blocks(raw):
 header,*chunks=re.split(rb'(?m)(?=^/--)',raw)
 assert chunks and chunks[-1].endswith(b'end AspisR1CuGamma\n')
 chunks[-1]=chunks[-1][:-len(b'end AspisR1CuGamma\n')]
 result={}
 for chunk in chunks:
  name=re.search(rb'(?m)^(?:def\s+|def\s*\n\s*|structure\s+|inductive\s+)([\w.]+)',chunk)
  assert name,chunk[:250]
  key=name[1].decode();assert key not in result,key;result[key]=chunk
 return header,result
strip_doc=lambda x:re.sub(rb'/--.*?-/',b'',x,flags=re.S).strip()
outputs={};removed={};rawpins={}
for filename,original in [('Types.lean','Types.lean'),('Funs.lean','Funs.lean')]:
 raw=(here/'cu-gamma-caller-generated'/filename).read_bytes();rawpins[filename]=hashlib.sha256(raw).hexdigest()
 header,new=blocks(raw);_,old=blocks((here/'cu-gamma-generated'/original).read_bytes())
 shared=[name for name in new if name in old]
 for name in shared:
  assert strip_doc(new[name])==strip_doc(old[name]),name
  del new[name]
 removed[filename]=shared
 if filename=='Types.lean':header=header.replace(b'import Aeneas\n',b'import AspisR1CuGamma.Funs\n')
 else:header+=b'variable [Boundaries] [CallerBoundaries]\n\n'
 outputs[filename]=header+b''.join(new.values())+b'end AspisR1CuGamma\n'
rawpins['FunsExternal_Template.lean']=hashlib.sha256((here/'cu-gamma-caller-generated/FunsExternal_Template.lean').read_bytes()).hexdigest()
manifest=dict(raw_inputs=rawpins,removed_identical_declarations=removed,
 scope='Reuse exact original nominal carriers and constants after byte-equality of declaration bodies. Complete new caller bodies unchanged; imports and universal class variables only. No preparation axiom is introduced: original checked preparations are imported.')
outputs['emission-layout.json']=(json.dumps(manifest,indent=2)+'\n').encode()
for name,raw in outputs.items():
 p=(here/'cu-gamma-caller-emission-layout.json') if name=='emission-layout.json' else area/'lean/AspisR1CuGammaCall'/name
 if args.check:assert p.read_bytes()==raw,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
print(json.dumps(dict(check=args.check,removed_identical=removed,complete_caller_bodies_unchanged=True)))
