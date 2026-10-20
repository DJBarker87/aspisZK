#!/usr/bin/env python3
"""Factor exact source blocks at already emitted helper boundaries; inverse checked."""
from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
tool=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();out=tool/'rho-accumulate-factored-input'
base=(tool/'rho-coefficients-input/lib.rs').read_bytes().split(b'pub mod rho_old {')[0]
basekit=(tool/'rho-coefficients-input/lib.rs').read_bytes()
modules=basekit[len(base):]
# Helpers are untouched complete coefficient bodies, already source pinned.
lib=basekit
originals={};factored={}
for side in ['old','new']:
 body=(tool/f'rho-accumulate-input/fragments/{side}-accumulate.rs').read_bytes()
 prefix_start=body.index(b'    let mut basis=');prefix_end=body.index(b'    for j in 0..a.weights.len()')
 prefix=body[prefix_start:prefix_end]
 coeff=(tool/f'rho-coefficients-input/fragments/{side}-original-loop.rs').read_bytes()
 assert body[prefix_end:prefix_end+len(coeff)]==coeff
 basis_body=prefix.replace(b'a.weights.len()',b'length')
 basis_name=b'source_basis_'+side.encode()
 lib+=b'\npub fn '+basis_name+b'(length:usize,mut node:aspis_core::field::M31)->[aspis_core::field::M31;256] {\nuse aspis_core::field::M31;\n'+basis_body+b'    basis\n}\n'
 basis_call=b'    let basis=crate::'+basis_name+b'(a.weights.len(),node);\n'
 coeff_call=b'    crate::rho_'+side.encode()+b'::coefficients(&mut a.weights,a.power,a.next,&basis'+(b',pending' if side=='new' else b'')+b');\n'
 changed=body.replace(prefix,basis_call,1).replace(coeff,coeff_call,1)
 assert changed.replace(basis_call,prefix,1).replace(coeff_call,coeff,1)==body
 declared=changed.replace(b'fn accumulate_with_node(',b'pub fn accumulate_with_node(',1)
 lib+=b'pub mod factored_'+side.encode()+b' {use crate::{verifier::{Prepared,Accumulator},aspis_core::field::{M31,WideExact as E},BatchedWeights};\n'+declared+b'\n}\n'
 originals[side]=sha(body);factored[side]=sha(changed)
outputs={'lib.rs':lib}
for n in ['Cargo.toml','Cargo.lock']:outputs[n]=(tool/'rho-coefficients-input'/n).read_bytes()
pins=json.loads((tool/'rho-coefficients-input/source-pins.json').read_text())
meta={**pins,'scope':'Complete original accumulate bodies factored into exact basis and coefficient source blocks. Inverse source substitution checked. No statement/body arithmetic edits. Actual source bindings for helpers still required.','original_accumulate_sha256':originals,'factored_accumulate_sha256':factored,'kit_files':{n:sha(b) for n,b in outputs.items()},'opaque_paths':pins['opaque_paths']+['crate::_::mul_qm31','crate::source_basis_old','crate::source_basis_new','crate::rho_old::coefficients','crate::rho_new::coefficients'],'roots':['crate::factored_old::accumulate_with_node','crate::factored_new::accumulate_with_node']}
outputs['source-pins.json']=(json.dumps(meta,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=out/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(b)
print(json.dumps({'check':a.check,'lib_sha256':sha(lib)}))
