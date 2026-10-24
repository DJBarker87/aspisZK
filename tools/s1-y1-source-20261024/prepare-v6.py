#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys,json,hashlib
P=Path(__file__).resolve().parent;O=Path(sys.argv[1])
subprocess.run([sys.executable,str(P/'prepare.py'),str(O)],check=True)
(O/'src/proofs.rs').write_bytes((P/'proofs-v6.rs').read_bytes())
p=O/'Cargo.toml';p.write_text(p.read_text()+'\n[profile.dev]\nopt-level = 3\noverflow-checks = true\n')
p=O/'source-binding.json';m=json.loads(p.read_text());m['scope']='Unchanged native claims-sized expansion, complete arbitrary buffers and every output byte via symbolic watch index. No reference execution, stubs, allocation claim or whole-caller transport. Complete reference content law must be proved separately in Lean.';m['files']={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file() and p.name!='source-binding.json'};p.write_text(json.dumps(m,indent=2)+'\n')
