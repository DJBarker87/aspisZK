#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument("--check",action="store_true");args=ap.parse_args()
tool=Path(__file__).resolve().parent;root=tool.parents[4];kit=tool/'canonical-reader-input'
rev='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';path='crates/aspis-r1-cost-probe/src/verifier.rs';src=subprocess.check_output(['git','-C',str(root),'show',rev+':'+path]);a=src.index(b'struct Reader');b=src.index(b'\n#[inline(never)]',a);reader=src[a:b];a0=src.index(b'pub enum Error');b0=src.index(b'\n',a0);err=src[a0:b0];sha=lambda b:hashlib.sha256(b).hexdigest()
files={'lib.rs':b'pub mod field;\nuse field::{WideExact as E,QM31 as K};\n'+err+b'\n'+reader+b'\n','Cargo.toml':b'[package]\nname="aspis-r1-canonical-reader"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n','Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-canonical-reader"\nversion = "0.0.0"\n'}
for n in ['field.rs','field/wide_exact.rs']:files[n]=(tool/'wide-arithmetic-input'/n).read_bytes()
files['source-pins.json']=(json.dumps(dict(revision=rev,path=path,file_sha256=sha(src),fragments=[dict(start=a,end=b,sha256=sha(reader)),dict(start=a0,end=b0,sha256=sha(err))],files={n:sha(b) for n,b in files.items()},scope='Exact Reader declaration and impl bytes, complete Error enum; module imports only. raw remains unchanged common source boundary.'),indent=2)+'\n').encode()
for n,b in files.items():
 p=kit/n
 if args.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print(json.dumps(dict(check=args.check,files=len(files),reader_bytes_unchanged=True)))
