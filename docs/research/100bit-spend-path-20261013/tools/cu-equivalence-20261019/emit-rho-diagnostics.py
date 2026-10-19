#!/usr/bin/env python3
"""Reuse identical source carriers/modulus; preserve every diagnostic body."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
def blocks(raw):
 header,*chunks=re.split(rb'(?m)(?=^/--)',raw)
 end=re.search(rb'\nend \w+\n$',chunks[-1]);assert end;chunks[-1]=chunks[-1][:end.start()]+b'\n'
 out={}
 for c in chunks:
  m=re.search(rb'(?m)^(?:def\s+|def\s*\n\s*|structure\s+|inductive\s+)([\w.]+)',c)
  if m is None:m=re.search(rb'\] def ([\w.]+)',c)
  assert m,c;out[m[1].decode()]=c
 return header,out
strip=lambda b:re.sub(rb'/--.*?-/',b'',b,flags=re.S).strip()
outputs={};shared={}
for name in ['Types.lean','Funs.lean']:
 raw=(here/'rho-diagnostics-generated'/name).read_bytes();header,new=blocks(raw);_,old=blocks((area/'lean/AspisR1CuRho'/name).read_bytes())
 common=[n for n in new if n in old]
 for n in common:assert strip(new[n])==strip(old[n]),n;del new[n]
 shared[name]=common
 if name=='Types.lean':header=header.replace(b'import Aeneas\n',b'import AspisR1CuRho.Types\n')
 else:header=header.replace(b'import Aeneas\n',b'import AspisR1CuRho.Funs\n')
 out=(header+b''.join(new.values())+b'end AspisR1RhoDiagnostics\n').replace(b'namespace AspisR1RhoDiagnostics\n',b'namespace AspisR1CuRho\n').replace(b'end AspisR1RhoDiagnostics\n',b'end AspisR1CuRho\n')
 outputs[name]=out
meta=dict(shared_byte_identical_declarations=shared,raw={n:sha((here/'rho-diagnostics-generated'/n).read_bytes()) for n in outputs},promoted={n:sha(b) for n,b in outputs.items()},adaptations=['Reuse identical original M31/CM31/QM31 carriers and field.P.','Set owner namespace to AspisR1CuRho; adjust imports. No generated diagnostic function body changes.'])
for n,b in outputs.items():
 p=area/'lean/AspisR1RhoDiagnostics'/n
 if args.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
p=here/'rho-diagnostics-layout.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if args.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=args.check,bodies_unchanged=True,shared=shared)))
