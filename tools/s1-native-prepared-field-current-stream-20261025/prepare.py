#!/usr/bin/env python3
"""Current source, actual field decoder, unchanged full native dot states generated at reached calls."""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1])
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-field-current-20261025/prepare.py'),str(O)],check=True)
p=O/'min/src/prepared_claim_native/proofs.rs';s=p.read_text()
changes=json.loads((T/'changes.json').read_text())
for a,b in changes:
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
p.write_text(s);(T/'proofs.rs').write_text(s)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'current-stream-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,freeze='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',changes=changes,normal_primitive_cuts=8,native_dot_carrier='Unchanged full native EbyKDot; all8u64sums andusizecount observed before every push andatfinish. Independent arbitrary reply at every reached call; single ghost previous-state register replaces unobserved indexed tape.',remaining='Native check required; canonical928-byte input domain,8 primitive cuts, SDK/init/extraction/runtime/oracle/release remain open.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',source_files=len(files),source_freeze='4bb3b3f51e',native_dot_carrier_unchanged=True)))
