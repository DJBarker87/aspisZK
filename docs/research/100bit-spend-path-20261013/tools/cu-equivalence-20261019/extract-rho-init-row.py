#!/usr/bin/env python3
"""Extract the exact initialization assignment expression, not the zip loop."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess

ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
root=Path(__file__).resolve().parents[5]
tool=Path(__file__).resolve().parent
# The reused carrier fragments must themselves remain exact production cuts.
subprocess.check_output(['python3',str(tool/'extract-rho.py'),'--check'],text=True)
source=root/'crates/aspis-r1-cost-probe/src/verifier.rs'
revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
raw=source.read_bytes()
assert raw==subprocess.check_output(['git','-C',str(root),'show',revision+':crates/aspis-r1-cost-probe/src/verifier.rs'])
matches=list(re.finditer(rb'\*out=(\[w\.c0\.a\.0 as u64,w\.c0\.b\.0 as u64,w\.c1\.a\.0 as u64,w\.c1\.b\.0 as u64\]);',raw))
assert len(matches)==1
match=matches[0];expression=match.group(1)
fields=b''.join((tool/'rho-input/fragments'/name).read_bytes()+b'\n' for name in ['m31.rs','cm31.rs','qm31.rs'])
outputs={
 'lib.rs':b'pub mod field {\n'+fields+b'}\npub fn row(w:&field::QM31)->[u64;4] {\n'+expression+b'\n}\n',
 'Cargo.toml':b'[package]\nname="aspis-r1-cu-rho-init-row"\nversion="0.0.0"\nedition="2021"\npublish=false\n[lib]\npath="lib.rs"\n[workspace]\n',
 'Cargo.lock':b'version = 4\n\n[[package]]\nname = "aspis-r1-cu-rho-init-row"\nversion = "0.0.0"\n',
}
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=dict(production_revision=revision,source_path=str(source.relative_to(root)),
 source_sha256=sha(raw),start_byte=match.start(1),end_byte_exclusive=match.end(1),
 expression_sha256=sha(expression),outputs={n:sha(b) for n,b in outputs.items()},
 scope='Exact assignment RHS under a free-function boundary. This does not extract new/zip, prove allocation, or admit the enclosing caller.')
outputs['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode()
for name,data in outputs.items():
 path=tool/'rho-init-row-input'/name
 if args.check:assert path.read_bytes()==data,name
 else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
print(json.dumps(dict(check=args.check,expression_sha256=sha(expression),files=len(outputs))))
