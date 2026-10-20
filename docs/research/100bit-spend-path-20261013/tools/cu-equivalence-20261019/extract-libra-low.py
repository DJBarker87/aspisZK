#!/usr/bin/env python3
from pathlib import Path
import subprocess,hashlib,json,argparse
ap=argparse.ArgumentParser();ap.add_argument("--check",action="store_true");args=ap.parse_args()
tool=Path(__file__).resolve().parent;root=tool.parents[4];kit=tool/'libra-low-input'
rev='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';path='crates/aspis-r1-cost-probe/src/weights.rs';src=subprocess.check_output(['git','-C',str(root),'show',rev+':'+path]);start=src.index(b'            let low:[E;16]=');end=src.index(b'\n',start);cut=src[start:end]
files={'lib.rs':b'pub mod field;\nuse field::{WideExact as E,M31};\nconst QUARTER:M31=M31(536870912);\nconst PERM:[usize;4]=[0,3,2,1];\npub fn low(ap0:&[E;4],ap1:&[E;4])->[E;16] {\n'+cut+b'\nlow\n}\n','Cargo.toml':b'[package]\nname="aspis-r1-libra-low"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n','Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-libra-low"\nversion = "0.0.0"\n'}
for n in ['field.rs','field/wide_exact.rs']:files[n]=(tool/'wide-arithmetic-input'/n).read_bytes()
sha=lambda b:hashlib.sha256(b).hexdigest()
files['source-pins.json']=(json.dumps(dict(revision=rev,path=path,file_sha256=sha(src),start_byte=start,end_byte_exclusive=end,fragment_sha256=sha(cut),kit_files={n:sha(b) for n,b in files.items()},source_context='Exact one low-array statement projected from unchanged Weights.pair body; wrapper returns local low. Original statement bytes unchanged.'),indent=2)+'\n').encode()
for n,b in files.items():
 p=kit/n
 if args.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=args.check,files=len(files),exact_low_statement=True)))
