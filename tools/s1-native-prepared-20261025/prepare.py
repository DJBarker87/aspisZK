#!/usr/bin/env python3
"""Materialize a fresh source-only native constructor probe; never executes it."""
from pathlib import Path
import argparse,hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
T=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--out',required=True);args=parser.parse_args()
O=Path(args.out);O.mkdir(mode=0o700,parents=False,exist_ok=False)
freeze='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
sha=lambda data:hashlib.sha256(data).hexdigest()
git=lambda path:subprocess.check_output(['git','show',freeze+':'+path],cwd=R)
get=lambda name:git('crates/aspis-r1-cost-probe/src/'+name).decode()
selected={};spans={}
def item(file,start,key):
    s=get(file);a=s.index(start);z=s.index('{',a)+1;depth=1
    while depth:
        depth+=(s[z]=='{')-(s[z]=='}');z+=1
    value=s[a:z];selected[key]=value
    spans[key]=dict(file=file,offset=a,length=z-a,sha256=sha(value.encode()),whole_source_sha256=sha(s.encode()))
    return value
verified=item('r1_semantic.rs','pub struct Verified<','Verified')
error=item('verifier.rs','#[derive(Debug,Clone,Copy,PartialEq,Eq)]\npub enum Error','Error')
view=item('verifier.rs','pub struct View<','View')
prepared=item('verifier.rs','pub struct Prepared ','Prepared')
new=item('verifier.rs','impl Prepared ','Prepared_impl')
claim=item('verifier.rs','fn prepared_claim<','prepared_claim')
powers=item('weights.rs','pub fn powers<','powers');field=item('weights.rs','pub fn field(','field')
payload={
 'r1_semantic.rs':'use alloc::boxed::Box;\nuse aspis_core::{Digest32,circle::SecureCirclePoint,field::QM31};\nuse crate::r1_wire::{Challenges,SemanticTranscript};\n'+verified+'\n',
 'verifier.rs':'use aspis_core::r0::CodeField;\nuse alloc::{boxed::Box,vec::Vec};\nuse aspis_core::{Digest32,field::{WideExact as E,QM31 as K},circle::SecureCirclePoint};\nuse crate::{transport::Variant,weights::{field,powers},transcript::Transcript};\n'+error+'\n'+view+'\n'+prepared+'\n'+claim+'\n'+new+'\n\n#[cfg(kani)]\n#[path="proofs.rs"]mod proofs;\n',
 'weights.rs':'use aspis_core::{field::WideExact as E,r0::CodeField};\n'+powers+'\n'+field+'\n',
 'transport.rs':get('transport.rs'),'fast_pairing.rs':get('fast_pairing.rs'),'trace.rs':get('trace.rs'),
 'transcript.rs':get('transcript.rs')+'\n#[cfg(kani)]\npub(crate) fn proof_input<H:Digest32>(hash:H,state:[u8;32])->Transcript<H>{Transcript{state,hash}}\n',
 'r1_wire.rs':get('r1_wire.rs')+'\n#[cfg(kani)]\nimpl<H:Digest32> SemanticTranscript<H>{pub(crate) fn proof_input(hash:H,state:[u8;32],next_row:u8)->Self{Self{state,hash,next_row}}}\n'}
files={}
def put(path,data):
    p=O/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);files[path]=sha(data)
base=json.loads((B/'evidence/s126-current-caller-20261021/s1-init-local-20261025/source-binding.json').read_text())
for row in base['native_source_files']:
    if row['path'].startswith('core-workspace/'):
        data=git(row['source']);assert sha(data)==row['sha256'];put(row['path'],data)
put('core-workspace/Cargo.toml',b'[workspace]\nmembers=["crates/aspis-core"]\nresolver="2"\n[workspace.package]\nedition="2021"\nlicense="MIT OR Apache-2.0"\nversion="0.1.0"\n')
for name,text in payload.items():put('min/src/prepared_native/'+name,text.encode())
put('min/src/prepared_native/proofs.rs',(T/'proofs.rs').read_bytes())
put('min/src/sampler.rs',get('sampler.rs').encode())
root='#![no_std]\nextern crate alloc;\npub mod sampler;\n'
for name in ['transport','fast_pairing','trace','r1_wire','r1_semantic','weights','transcript','verifier']:
    root+=f'#[path="prepared_native/{name}.rs"] pub mod {name};\n'
put('min/src/probe_prepared.rs',root.encode())
put('min/Cargo.toml',b'''[package]
name="aspis-r1-cost-probe"
version="0.1.0"
edition="2021"
[workspace]
[features]
default=["private-leaf-salts"]
private-leaf-salts=[]
prover=[]
r1p-check=[]
[dependencies]
aspis-core={path="../core-workspace/crates/aspis-core",features=["r0"]}
[profile.release]
opt-level=3
overflow-checks=true

[profile.dev]
opt-level=3
overflow-checks=true
[profile.dev.build-override]
opt-level=3

[lib]
path="src/probe_prepared.rs"
''')
put('min/Cargo.lock',(B/'evidence/s126-current-caller-20261021/s1-init-local-20261025/original-min/Cargo.lock').read_bytes())
(O/'binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=freeze,
    selected=selected,selected_spans=spans,payload_files={k:sha(v.encode())for k,v in payload.items()},files=files,
    qualification='Selected complete declarations/bodies with adjusted imports; complete frozen sibling modules; two proof-only state constructors and proof module appended. Not a whole crate/context/ABI/source-artifact identity result.',
    compiler_launched=False,solver_launched=False,host_SSH_operations=0),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),directory=str(O))))
