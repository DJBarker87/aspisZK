#!/usr/bin/env python3
"""Reuse the exact core error carrier; parameterize only external reserve."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1]
raw_types=(here/'rho-heap-generated/Types.lean').read_bytes();raw_funs=(here/'rho-heap-generated/Funs.lean').read_bytes()
pattern=rb'(?m)^inductive r0.Error where\n(?:\|[^\n]+\n)+'
core=re.search(pattern,raw_types)[0];existing=(area/'lean/AspisR1RhoInit/Types.lean').read_bytes()
assert core==re.search(pattern,existing)[0]
types=raw_types.replace(b'@[discriminant isize]\n'+core,b'').replace(b'namespace AspisR1RhoHeap\n',b'namespace AspisR1CuRho\n').replace(b'end AspisR1RhoHeap\n',b'end AspisR1CuRho\n')
types=re.sub(rb'/-- \[aspis_r1_rho_heap::r0::Error\].*?-/\n',b'',types,flags=re.S)
funs=raw_funs.replace(b'namespace AspisR1RhoHeap\n',b'namespace AspisR1CuRho\nvariable [HeapReserve]\n').replace(b'end AspisR1RhoHeap\n',b'end AspisR1CuRho\n')
outputs={'Types.lean':types,'Funs.lean':funs}
meta=dict(raw_types_sha256=hashlib.sha256(raw_types).hexdigest(),raw_funs_sha256=hashlib.sha256(raw_funs).hexdigest(),
    promoted={n:hashlib.sha256(b).hexdigest() for n,b in outputs.items()},
    adaptations=['Reuse identical original r0.Error declaration; omit its duplicate unused discriminator registration.',
        'Set owner namespace to AspisR1CuRho and add the explicit reserve boundary variable.',
        'All generated function bodies unchanged. External reserve error type and operation are universally parameterized; no axiom template is imported.'])
for name,data in outputs.items():
    p=area/'lean/AspisR1RhoHeap'/name
    if args.check:assert p.read_bytes()==data,name
    else:p.parent.mkdir(exist_ok=True);p.write_bytes(data)
p=here/'rho-heap-layout.json';data=(json.dumps(meta,indent=2)+'\n').encode()
if args.check:assert p.read_bytes()==data
else:p.write_bytes(data)
print(json.dumps(dict(check=args.check,whole_function_bodies_unchanged=True)))
