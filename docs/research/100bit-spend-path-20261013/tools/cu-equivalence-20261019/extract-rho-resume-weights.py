#!/usr/bin/env python3
"""Exact checkpoint weight-decode traversal factored for local source proof."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611';loop=b'for x in &mut weights {*x=r.k()?;}';ident=[];outputs={}
for revision in [candidate+'^',candidate,'39c2971dd16c95858a4cfd2c9ae35da052eacfa9']:
 raw=subprocess.check_output(['git','-C',str(repo),'show',revision+':crates/aspis-r1-cost-probe/src/verifier.rs'])
 with tempfile.NamedTemporaryFile() as f:
  f.write(raw);f.flush();resume,*_=cut.find_item(Path(f.name),'pub fn resume<')
 assert resume.count(loop)==1
 ident.append(dict(revision=revision,resume_sha256=sha(resume),weight_loop_sha256=sha(loop)))
 if revision==candidate:outputs['fragments/resume.rs']=resume
assert all(x['resume_sha256']==ident[0]['resume_sha256'] for x in ident)
base=(here/'rho-reader-input/lib.rs').read_bytes();assert base.endswith(b'\n}\n}\n')
# Keep the method impl closed; insert helper into its original verifier module.
lib=b'extern crate alloc;\n'+base[:-2]+b'\nfn resume_weights<\'a>(mut weights:alloc::vec::Vec<K>,mut r:Reader<\'a>)->Result<(alloc::vec::Vec<K>,Reader<\'a>),Error> {\n    '+loop+b'\n    Ok((weights,r))\n}\n}\n'
outputs.update({'lib.rs':lib,'Cargo.toml':b'[package]\nname="aspis-r1-rho-resume-weights"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n','Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-rho-resume-weights"\nversion = "0.0.0"\n'})
pins=dict(candidate=candidate,source_identity=ident,source_loop=loop.decode(),base_reader_kit_sha256=sha(base),features=[],roots=['crate::verifier::resume_weights'],opaque_paths=['crate::verifier::_::k'],kit_files={n:sha(b) for n,b in outputs.items()},scope='Exact complete original resume weight-decode loop factored into a function owning both original local variables weights and Reader. Loop bytes unchanged, Reader/k source unchanged. Final Ok((weights,r)) is the helper continuation; original local ownership is retained. Full resume caller context composition remains separate. Reader.k binds to exact checked source, not an assumed canonical callback.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for n,b in outputs.items():
 p=here/'rho-resume-weights-input'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=a.check,source_loop_unchanged=True)))
