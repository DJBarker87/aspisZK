#!/usr/bin/env python3
"""Fresh source-only reconstruction; no compiler or solver and no production edits."""
from pathlib import Path
import argparse,hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--out',required=True);a=p.parse_args();O=Path(a.out)
assert not O.exists()
subprocess.run(['python3',str(R/'tools/s1-native-prepared-20261025/prepare.py'),'--out',str(O)],check=True)
(O/'binding.json').rename(O/'predecessor-binding.json')
(O/'min/src/prepared_native').rename(O/'min/src/prepared_transcript_native')
(O/'min/src/prepared_transcript_native/proofs.rs').write_bytes((T/'proofs.rs').read_bytes())
(O/'min/src/probe_prepared.rs').unlink()
(O/'min/src/probe_prepared_transcript.rs').write_bytes((T/'probe.rs').read_bytes())
c=O/'min/Cargo.toml';c.write_text(c.read_text().replace('probe_prepared.rs','probe_prepared_transcript.rs'))
# Preserve three inactive files inventoried by the warm workspace; none is
# selected by Cargo's explicit lib path. Pin without treating them as imports.
for name in ['claims_write_proofs.rs','r1_wire.rs','lib.rs']:
 src=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-claims-row-step-20261024/extra/uninit-min/src'/name
 (O/'min/src'/name).write_bytes(src.read_bytes())
files={str(f.relative_to(O)):hashlib.sha256(f.read_bytes()).hexdigest() for f in O.rglob('*') if f.is_file()}
(O/'binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,compiler_launched=False,solver_launched=False,qualification='Exact frozen selected bodies, complete release carriers and sibling modules, adjusted imports and proof-only constructors; not whole crate/context/ABI identity.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files))))
