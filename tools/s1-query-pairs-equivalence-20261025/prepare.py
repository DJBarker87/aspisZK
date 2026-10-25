#!/usr/bin/env python3
"""Actual current core queries_from_pairs vs an owned indexed full-result reference."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1]);F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-field-current-stream-20261025/prepare.py'),str(O)],check=True)
code=(T/'proofs.rs').read_text();(O/'min/src/probe_query.rs').write_text(code)
p=O/'min/Cargo.toml';p.write_text(p.read_text().replace('src/probe_prepared_claim.rs','src/probe_query.rs'))
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'query-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,freeze=F,domain='All eight32-byte blocks andall eight32-byte advances. Complete accepted22-array andselected32-byte state, or exact native rejection error. No stubs/canonicality/distinctness assumptions.',remaining='Native equality pending; owned reference then needs Lean source/model driver binding. No SDK/oracle/release closure.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),normal_cuts=0)))
