#!/usr/bin/env python3
"""Factor the exact common power/counter suffix; caller composition remains open."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611';suffix=b'a.power=a.power.mul(p.rho);a.next+=1;';ident=[]
base=(here/'rho-accumulate-input/lib.rs').read_bytes()
for revision in [candidate+'^',candidate]:
 raw=subprocess.check_output(['git','-C',str(repo),'show',revision+':crates/aspis-r1-cost-probe/src/verifier.rs'])
 with tempfile.NamedTemporaryFile() as f:
  f.write(raw);f.flush();fn,*_=cut.find_item(Path(f.name),'fn accumulate_with_node(')
  assert fn.count(suffix)==1 and fn.rstrip().endswith(suffix+b'\n}')
  carriers={}
  for anchor in ['pub struct Prepared {','pub struct Accumulator {']:
   item,*_=cut.find_item(Path(f.name),anchor);assert item in base;carriers[anchor]=sha(item)
 ident.append(dict(revision=revision,function_sha256=sha(fn),suffix_sha256=sha(suffix),carrier_sha256=carriers))
assert ident[0]['carrier_sha256']==ident[1]['carrier_sha256']
lib=base+b'\npub fn power_tail(p:&verifier::Prepared,a:&mut verifier::Accumulator) {\n    '+suffix+b'\n}\n'
outputs={'lib.rs':lib,'Cargo.toml':b'[package]\nname="aspis-r1-rho-power-tail"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n','Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-rho-power-tail"\nversion = "0.0.0"\n'}
outputs['Cargo.toml']+=b'[features]'+(here/'rho-accumulate-input/Cargo.toml').read_bytes().split(b'[features]',1)[1]
pins=dict(candidate=candidate,source_identity=ident,base_input_sha256=sha(base),features=['r0','private-leaf-salts'],roots=['crate::power_tail'],opaque_paths=['crate::aspis_core::field::_::mul'],suffix=suffix.decode(),kit_files={n:sha(b) for n,b in outputs.items()},scope='Exact shared suffix factored into a function with the original complete Prepared/Accumulator carriers. Every suffix byte is unchanged. Prefix and source caller composition remain open; no wide-field RHS operation is claimed by this local tail lemma.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=here/'rho-power-tail-input'/n
 if args.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=args.check,common_source_suffix_identical=True)))
