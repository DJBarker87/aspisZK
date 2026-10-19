#!/usr/bin/env python3
"""Share identical field carriers and retain the exact emitted scalar_k body."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(here/'rho-scalar-k-generated/Types.lean').read_bytes();header,*chunks=re.split(rb'(?m)(?=^/--)',raw);end=re.search(rb'\nend \w+\n$',chunks[-1]);assert end;chunks[-1]=chunks[-1][:end.start()]+b'\n'
existing=(area/'lean/AspisR1CuRho/Types.lean').read_bytes()+(area/'lean/AspisR1RhoDiagnostics/Types.lean').read_bytes();kept=[];shared=[]
for c in chunks:
 m=re.search(rb'(?m)^(?:def\s+|structure\s+)([\w.]+)',c);assert m;name=m[1]
 if not name.startswith(b'field.') :kept.append(c);continue
 clean=re.sub(rb'/--.*?-/',b'',c,flags=re.S).strip();assert clean in existing,name;shared.append(name.decode())
types=(header.replace(b'import Aeneas\n',b'import AspisR1RhoDiagnostics.Types\n')+b''.join(kept)+b'end AspisR1RhoScalarK\n').replace(b'namespace AspisR1RhoScalarK\n',b'namespace AspisR1CuRho\n').replace(b'end AspisR1RhoScalarK\n',b'end AspisR1CuRho\n')
raw_funs=(here/'rho-scalar-k-generated/Funs.lean').read_bytes();funs=raw_funs.replace(b'namespace AspisR1RhoScalarK\n',b'namespace AspisR1CuRho\nvariable [ScalarKBlocks]\n').replace(b'end AspisR1RhoScalarK\n',b'end AspisR1CuRho\n')
outputs={'Types.lean':types,'Funs.lean':funs}
for n,b in outputs.items():
 p=area/'lean/AspisR1RhoScalarK'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
meta=dict(shared_identical_declarations=shared,raw_types_sha256=sha(raw),raw_funs_sha256=sha(raw_funs),promoted={n:sha(b) for n,b in outputs.items()},adaptations=['Reuse byte-identical current field carriers.','Set namespace owner AspisR1CuRho and add explicit common block boundary binder; no generated function body changes.'])
p=here/'rho-scalar-k-layout.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=a.check,source_scalar_k_body_unchanged=True)))
