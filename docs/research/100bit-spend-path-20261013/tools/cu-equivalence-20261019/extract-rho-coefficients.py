#!/usr/bin/env python3
"""Extract complete coefficient loops with explicit stable accumulator projections."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((here/'rho-accumulate-input/source-pins.json').read_text())
base=(here/'rho-accumulate-input/lib.rs').read_bytes().split(b'pub mod rho_old {')[0]
outputs={};lib=base
for side in ['old','new']:
 raw=(here/f'rho-accumulate-input/fragments/{side}-accumulate.rs').read_bytes()
 begin=raw.index(b'    for j in 0..a.weights.len() {');end=raw.index(b'    a.rhs=')
 body=raw[begin:end]
 substitutions=[(b'a.weights',b'rows'),(b'a.power',b'power'),(b'a.next',b'next')]
 normalized=body
 for original,local in substitutions: normalized=normalized.replace(original,local)
 inverse=normalized
 for original,local in substitutions: inverse=inverse.replace(local,original)
 assert inverse==body
 pending=b',mut pending:Option<&mut BatchedWeights>' if side=='new' else b''
 helper=b'pub fn coefficients(rows:&mut alloc::vec::Vec<aspis_core::field::QM31>,power:aspis_core::field::QM31,next:usize,basis:&[M31;256]'+pending+b') {\n'+normalized+b'}\n'
 outputs[f'fragments/{side}-original-loop.rs']=body;outputs[f'fragments/{side}-helper.rs']=helper
 lib+=b'pub mod rho_'+side.encode()+b' {use crate::{aspis_core,aspis_core::field::{M31,WideExact as E},BatchedWeights};\n'+helper+b'}\n'
outputs['lib.rs']=lib
for name in ['Cargo.toml','Cargo.lock']:outputs[name]=(here/'rho-accumulate-input'/name).read_bytes()
meta=dict(candidate=pins['candidate'],parent=pins['parent'],source=pins['source'],source_sha256=pins['source_sha256'],
 base_kit_sha256=sha(base),features=pins['features'],opaque_paths=pins['opaque_paths']+['crate::_::mul_m31'],
 roots=['crate::rho_old::coefficients','crate::rho_new::coefficients'],kit_files={n:sha(b) for n,b in outputs.items()},
 substitutions={'a.weights':'rows','a.power':'power','a.next':'next'},
 scope='Complete paired coefficient loops and pending term increment. Stable power and next projected to copied arguments and weights projected to the unique mutable subfield; inverse text substitution checked. The resulting field projection/factoring still requires enclosing caller interpretation, not an assumed full function equivalence. Arithmetic, trace and push/value opaque boundaries require bindings.')
outputs['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode()
for name,data in outputs.items():
 p=here/'rho-coefficients-input'/name
 if args.check:assert p.read_bytes()==data,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
print(json.dumps(dict(check=args.check,lib_sha256=sha(lib))))
