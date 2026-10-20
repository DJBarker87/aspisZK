#!/usr/bin/env python3
"""Exact old/new four-dot source kit; unchanged shared arithmetic stays shared."""
from pathlib import Path
import argparse, hashlib, json, subprocess

ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;repo=here.parents[4]
revision='e58b87665233febecc1b1a75c506eac1a8b72e00'
candidate='e58b87665233febecc1b1a75c506eac1a8b72e00'
sha=lambda b:hashlib.sha256(b).hexdigest()
def at(rev,path):
    return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
paths={
 'field.rs':'crates/aspis-core/src/field.rs',
 'field/wide_exact.rs':'crates/aspis-core/src/field/wide_exact.rs',
 'new_pairing.rs':'crates/aspis-r1-cost-probe/src/fast_pairing.rs',
}
outputs={};pins={}
for name,path in paths.items():
    raw=at(candidate,path)
    if name!='new_pairing.rs':assert raw==at(candidate+'^',path),path
    outputs[name]=raw;pins[name]=dict(path=path,revision=candidate,sha256=sha(raw))
old=at(candidate+'^',paths['new_pairing.rs'])
outputs['old_pairing.rs']=old
pins['old_pairing.rs']=dict(path=paths['new_pairing.rs'],revision=candidate+'^',sha256=sha(old))
delta=at(candidate,paths['new_pairing.rs'])
outputs['lib.rs']=b'''extern crate self as aspis_core;
pub mod field;
pub mod old_pairing;
pub mod new_pairing;
'''
outputs['Cargo.toml']=b'''[package]
name="aspis-r1-cu-canonical-dots"
version="0.0.0"
edition="2021"
publish=false
[lib]
path="lib.rs"
[workspace]
'''
outputs['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-cu-canonical-dots"\nversion = "0.0.0"\n'
metadata=dict(producing_revision=revision,candidate=candidate,sources=pins,
    candidate_body_sha256=sha(delta),
    parent_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse',candidate+'^'],text=True).strip(),
    kit_files={n:sha(b) for n,b in outputs.items()},
    scope='Candidate 5 complete exact old/new fast_pairing and shared unchanged arithmetic source files. Only crate/module boundary added. Parametric comparison may abstract identical arithmetic callees; no axiom template admitted.')
outputs['source-pins.json']=(json.dumps(metadata,indent=2)+'\n').encode()
for name,data in outputs.items():
    target=here/'cu-canonical-dots-input'/name
    if args.check:assert target.read_bytes()==data,name
    else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
print(json.dumps(dict(check=args.check,files=len(outputs),exact_candidate_and_parent=True)))
