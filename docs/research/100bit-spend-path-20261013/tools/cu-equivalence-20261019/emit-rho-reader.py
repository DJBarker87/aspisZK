#!/usr/bin/env python3
"""Promote complete emitted Reader bodies onto identical existing carriers."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(here/'rho-reader-generated/Types.lean').read_bytes();header,*chunks=re.split(rb'(?m)(?=^/--)',raw);end=re.search(rb'\nend \w+\n$',chunks[-1]);assert end;chunks[-1]=chunks[-1][:end.start()]+b'\n'
existing=(area/'lean/AspisR1CuRho/Types.lean').read_bytes()+(area/'lean/AspisR1RhoInit/Types.lean').read_bytes()
kept=[];shared=[]
for c in chunks:
 m=re.search(rb'(?m)^(?:def\s+|structure\s+|inductive\s+)([\w.]+)',c);assert m;name=m[1]
 if name==b'verifier.Reader':kept.append(c);continue
 clean=re.sub(rb'/--.*?-/',b'',c,flags=re.S).replace(b'@[discriminant isize]\n',b'').strip()
 assert clean in existing,name;shared.append(name.decode())
types=(header.replace(b'import Aeneas\n',b'import AspisR1CuRho.Types\nimport AspisR1RhoInit.Types\n')+b''.join(kept)+b'end AspisR1RhoReader\n').replace(b'namespace AspisR1RhoReader\n',b'namespace AspisR1CuRho\n').replace(b'end AspisR1RhoReader\n',b'end AspisR1CuRho\n')
raw_funs=(here/'rho-reader-generated/Funs.lean').read_bytes();assert b'read_discriminant' not in raw_funs
funs=raw_funs.replace(b'namespace AspisR1RhoReader\n',b'namespace AspisR1CuRho\n').replace(b'end AspisR1RhoReader\n',b'end AspisR1CuRho\n')
outputs={'Types.lean':types,'Funs.lean':funs}
for n,b in outputs.items():
 p=area/'lean/AspisR1RhoReader'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
meta=dict(shared_identical_declarations=shared,raw_types_sha256=sha(raw),raw_funs_sha256=sha(raw_funs),promoted={n:sha(b) for n,b in outputs.items()},adaptations=['Reuse identical original field carriers and verifier.Error; omit its unused duplicate discriminant registration.','Change namespace owner only. All generated Reader declaration and function bodies unchanged. Parser/Option functions bind to the existing strict source parser slice, with no axiom template imported.'])
p=here/'rho-reader-layout.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=a.check,whole_reader_bodies_unchanged=True)))
