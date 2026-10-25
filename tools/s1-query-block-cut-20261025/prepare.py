#!/usr/bin/env python3
"""Actual current core queries_from_pairs vs an owned indexed full-result reference."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1]);F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-field-current-stream-20261025/prepare.py'),str(O)],check=True)
p=O/'core-workspace/crates/aspis-core/src/r0_transcript.rs';original=p.read_text();p.write_text(original+(T/'wrapper.rs').read_text())
code=(T/'proofs.rs').read_text();(O/'min/src/probe_block.rs').write_text(code)
p=O/'min/Cargo.toml';p.write_text(p.read_text().replace('src/probe_prepared_claim.rs','src/probe_block.rs'))
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'query-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,freeze=F,domain='Every32-byte block, every22-word buffer, accepted_len<=22 anddraws<=64. Entire post-buffer/counts/stop flag equal and range invariant preserved. Two membership cuts: original generic slice contains at the reached u32 instance, and the exact owned_contains. Arbitrary common Bool replies; universal observer call0..7 andcell0..21 checks every ordered prefix/candidate/length/callcount pointwise; observer choices do not influence replies or scanner control; no distinctness premise. Relative control/trace check, not uncut native equality. Proof-only appended private-state wrapper; scan body unchanged.',remaining='Native equality pending; owned reference then needs Lean source/model driver binding. No SDK/oracle/release closure.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),normal_cuts=2)))
