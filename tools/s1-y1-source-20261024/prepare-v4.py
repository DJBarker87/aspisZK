#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys,json,hashlib
P=Path(__file__).resolve().parent;O=Path(sys.argv[1])
subprocess.run([sys.executable,str(P/'prepare.py'),str(O)],check=True)
p=O/'src/lib.rs';p.write_text(p.read_text()+'\n'+(P/'owned-v2.rs').read_text())
proof=(P/'proofs-v2.rs').read_text();proof=proof[:proof.index('// Split out')]
(O/'src/proofs.rs').write_text(proof)
p=O/'Cargo.toml';p.write_text(p.read_text()+'\n[profile.dev]\nopt-level = 3\noverflow-checks = true\n')
p=O/'source-binding.json';m=json.loads(p.read_text());m['reference_source']=(P/'owned-v2.rs').read_text();m['reference_sha256']=hashlib.sha256((P/'owned-v2.rs').read_bytes()).hexdigest();m['scope']='Fixed Y1 unchanged native/owned-reference all-byte equality. Complete buffers and result; owned helper calls end all borrows before loop edges. No stubs, production adoption or universal SDK/caller instance.';m['files']={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file() and p.name!='source-binding.json'};p.write_text(json.dumps(m,indent=2)+'\n')
