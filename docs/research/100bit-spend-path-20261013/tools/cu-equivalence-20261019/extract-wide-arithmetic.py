#!/usr/bin/env python3
"""Pin actual unchanged WideExact arithmetic and source QM31 dependencies."""
from pathlib import Path
import argparse,subprocess,json,hashlib
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
t=Path(__file__).resolve().parent;repo=t.parents[4];rev='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';out={};pins={};sha=lambda b:hashlib.sha256(b).hexdigest()
for n in ['field.rs','field/wide_exact.rs']:
 path='crates/aspis-core/src/'+n;data=subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path]);out[n]=data;pins[n]={'path':path,'file_sha256':sha(data)}
out['lib.rs']=b'pub mod field;\n'
out['Cargo.toml']=b'[package]\nname="aspis-r1-wide-arithmetic"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n'
out['Cargo.lock']=b'version = 4\n\n[[package]]\nname = "aspis-r1-wide-arithmetic"\nversion = "0.0.0"\n'
out['source-pins.json']=(json.dumps(dict(revision=rev,sources=pins,kit_files={n:sha(b) for n,b in out.items()},scope='Full exact field sources; only crate/module layout. M31/CM31/QM31 add/mul bind previously checked exact source through carrier transport; all selected Wide and sub/square/scalar operations emitted in full.'),indent=2)+'\n').encode()
for n,b in out.items():
 dest=t/'wide-arithmetic-input'/n
 if a.check:assert dest.read_bytes()==b
 else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
print(json.dumps({'check':a.check,'files':len(out)}))
