#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys,json,hashlib
P=Path(__file__).resolve().parent;O=Path(sys.argv[1])
subprocess.run([sys.executable,str(P/'prepare-v2.py'),str(O)],check=True)
(O/'src/proofs.rs').write_bytes((P/'proofs-v3.rs').read_bytes())
p=O/'source-binding.json';m=json.loads(p.read_text());m['scope']='Fixed Y1 input, output length <=1856 and !=928. Native rejection/frame with an ASSERTED unreachable chunks constructor cut; positive whole-native/reference proof is separately unstubbed. Not universal metadata/caller closure.';m['stub']={'target':'<[u8]>::chunks_exact','replacement':'forbidden_chunks<T>','body':'panic: any reached call fails verification','not_assumed_unreachable':True};m['files']={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*') if p.is_file() and p.name!='source-binding.json'};p.write_text(json.dumps(m,indent=2)+'\n')
