#!/usr/bin/env python3
"""Actual scalar selector/push source steps. No arithmetic stubs or reduced types."""
from pathlib import Path
import json,hashlib,subprocess,sys,re
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists();(O/'src').mkdir(parents=True)
REV='25866ec331cc7ce27dd9956609c11d32fa8fa58a';C='crates/aspis-r1-cost-probe/src/'
get=lambda p:subprocess.check_output(['git','-C',str(R),'show',REV+':'+p],text=True)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
v=get(C+'verifier.rs');a=v.index('fn prepared_claim<');b=v.index('{',a)+1;depth=1
while depth:depth+=(v[b]=='{')-(v[b]=='}');b+=1
original=v[a:b];match=re.search(r'let scalar=(match point \{.*?\});',original);assert match;expr=match[1]
selector='fn scalar_helper<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],point:usize,l:usize)->K { '+expr+' }'
step='''fn original_step<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize,l:usize,dot:&mut crate::fast_pairing::EbyKDot)->Result<(),Error> {
'''+match[0]+'''
 dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
 Ok(())
}
fn helper_step<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],g:&[E;29],point:usize,l:usize,dot:&mut crate::fast_pairing::EbyKDot)->Result<(),Error> {
 let scalar=scalar_helper(sem,y1,point,l);
 dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
 Ok(())
}
'''
fission=json.loads((R/'docs/research/100bit-spend-path-20261013/lean-candidates/s1-claim-fission-sum-proved-candidate-20261020/measurements/build/claim-transform.json').read_text())['after'].replace('fn prepared_claim<','fn fission_claim<')
code='''#![allow(dead_code)]
extern crate alloc;
use aspis_core::{Digest32,field::{WideExact as E,QM31 as K},r0::CodeField};
use aspis_r1_cost_probe::{weights::{field,powers},verifier::Error};
pub use aspis_r1_cost_probe::{r1_semantic,trace};
pub mod fast_pairing;
'''+original+'\n'+selector+'\n'+step+'\n'+fission+'\n#[cfg(kani)] mod proofs;\n'
(O/'src/lib.rs').write_text(code);(O/'src/fast_pairing.rs').write_text(get(C+'fast_pairing.rs'));(O/'src/proofs.rs').write_bytes((Path(__file__).parent/'proofs.rs').read_bytes())
(O/'Cargo.toml').write_text('''[package]
name="aspis-s1-claim-source-steps"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
aspis-core={path="/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core",features=["r0"]}
aspis-r1-cost-probe={path="frozen-probe"}
[profile.release]
opt-level=3
overflow-checks=true
''')
# Isolate the entire adopted cost-probe source, including its actual nominal
# Verified, transcript, field accessor and release trace definitions.
probe=O/'frozen-probe';(probe/'src').mkdir(parents=True)
files=subprocess.check_output(['git','-C',str(R),'ls-tree','-r','--name-only',REV,'crates/aspis-r1-cost-probe/'],text=True).splitlines()
for name in files:
 if not name.endswith('.rs'):continue
 dest=probe/Path(name).relative_to('crates/aspis-r1-cost-probe');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(get(name))
manifest=get('crates/aspis-r1-cost-probe/Cargo.toml').replace('edition.workspace = true','edition = "2021"').replace('license.workspace = true','license = "MIT OR Apache-2.0"').replace('version.workspace = true','version = "0.1.0"')
base='/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/'
def path_replace(m):
 from posixpath import normpath
 return 'path = "'+normpath(base+'crates/aspis-r1-cost-probe/'+m[1])+'"'
manifest=re.sub(r'path = "([^"]+)"',path_replace,manifest)
for name,version in [('serde_json','1.0.145'),('sha2','0.10.8'),('getrandom','0.3.4')]:
 manifest=manifest.replace(name+' = { workspace = true,',name+' = { version = "'+version+'",')
(probe/'Cargo.toml').write_text(manifest)
(O/'source-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',revision=REV,source_files={p:sha(get(C+p)) for p in ['verifier.rs','fast_pairing.rs','r1_semantic.rs','r1_wire.rs','weights.rs','trace.rs']},original_claim=original,scalar_expression=expr,original_statement=match[0],selector=selector,steps=step,source_step_sha256=sha(code),qualification=__doc__,remaining='Step/fission loop composition and original parent/source correspondence. A successful step check alone is not whole S1 closure.'),indent=2)+'\n')
