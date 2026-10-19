#!/usr/bin/env python3
"""Reuse exact original carriers; keep all normalized-wrapper bodies unchanged."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1]
def blocks(raw):
    header,*chunks=re.split(rb'(?m)(?=^/--)',raw)
    ending=re.search(rb'\nend \w+\n$',chunks[-1]);assert ending
    chunks[-1]=chunks[-1][:ending.start()]+b'\n'
    out={}
    for chunk in chunks:
        name=re.search(rb'(?m)^(?:def\s+|def\s*\n\s*|structure\s+|inductive\s+)([\w.]+)',chunk);assert name
        out[name[1].decode()]=chunk
    return header,out
strip=lambda b:re.sub(rb'/--.*?-/',b'',b,flags=re.S).strip()
raw_types=(here/'rho-init-wrapper-generated/Types.lean').read_bytes()
header,new=blocks(raw_types);_,old=blocks((area/'lean/AspisR1CuRho/Types.lean').read_bytes())
shared=[name for name in new if name in old]
for name in shared:assert strip(new[name])==strip(old[name]),name;del new[name]
types=(header.replace(b'import Aeneas\n',b'import AspisR1CuRho.Types\n')+b''.join(new.values())+b'end AspisR1CuRho\n').replace(b'namespace AspisR1RhoInit\n',b'namespace AspisR1CuRho\n')
raw_funs=(here/'rho-init-wrapper-generated/Funs.lean').read_bytes()
assert b'read_discriminant' not in raw_funs
assert types.count(b'@[discriminant isize]\n')==2
types=types.replace(b'@[discriminant isize]\n',b'')
funs=raw_funs.replace(b'namespace AspisR1RhoInit\n',b'namespace AspisR1CuRho\nvariable [InitAllocation]\n').replace(b'end AspisR1RhoInit\n',b'end AspisR1CuRho\n')
outputs={'Types.lean':types,'Funs.lean':funs}
manifest=dict(shared_identical_carriers=shared,raw_types_sha256=hashlib.sha256(raw_types).hexdigest(),raw_funs_sha256=hashlib.sha256(raw_funs).hexdigest(),
    promoted={n:hashlib.sha256(b).hexdigest() for n,b in outputs.items()},
    adaptations=['Reuse byte-identical field/BatchedWeights declarations from the checked original namespace.',
        'Set declaration-owner namespace to AspisR1CuRho, sharing those nominal carriers.',
        'Omit two unconsumed discriminant registrations whose generated global instance names collide with the original reference module. Inductive declarations and all function bodies are unchanged; no discriminant operation occurs in this wrapper.',
        'Add the explicit generic heap boundary variable; no generated function body changes.'])
for name,data in outputs.items():
    p=area/'lean/AspisR1RhoInit'/name
    if args.check:assert p.read_bytes()==data,name
    else:p.parent.mkdir(exist_ok=True);p.write_bytes(data)
p=here/'rho-init-wrapper-layout.json';data=(json.dumps(manifest,indent=2)+'\n').encode()
if args.check:assert p.read_bytes()==data
else:p.write_bytes(data)
print(json.dumps(dict(check=args.check,shared=shared,generated_function_bodies_unchanged=True)))
