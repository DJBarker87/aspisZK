#!/usr/bin/env python3
"""Fresh source-only materialization; no compiler, solver or production writes."""
from pathlib import Path
import argparse,hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--out',required=True);p.add_argument('--copied-inputs',action='store_true');p.add_argument('--prefix145',action='store_true');p.add_argument('--halves',action='store_true');a=p.parse_args();O=Path(a.out);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s1-native-prepared-transcript-20261025/prepare.py'),'--out',str(O)],check=True)
(O/'binding.json').rename(O/'transcript-binding.json')
D=O/'min/src/prepared_claim_native';(O/'min/src/prepared_transcript_native').rename(D)
(D/'proofs.rs').write_bytes((T/('proofs-halves.rs' if a.halves else ('proofs-prefix145.rs' if a.prefix145 else ('proofs-copied.rs' if a.copied_inputs else 'proofs.rs')))).read_bytes())
(O/'min/src/probe_prepared_transcript.rs').unlink();(O/'min/src/probe_prepared_claim.rs').write_bytes((T/'probe.rs').read_bytes())
c=O/'min/Cargo.toml';c.write_text(c.read_text().replace('probe_prepared_transcript.rs','probe_prepared_claim.rs'))
b=json.loads((T/'source-binding.json').read_text())['dot_helpers'];f=D/'fast_pairing.rs'
assert hashlib.sha256(f.read_bytes()).hexdigest()==b['original_sha256']
s=f.read_text();s=s.replace(b['insertion_after'],b['insertion_after']+b['insertion'],1)+b['append'];f.write_text(s)
assert hashlib.sha256(f.read_bytes()).hexdigest()==b['instrumented_sha256']
files={str(f.relative_to(O)):hashlib.sha256(f.read_bytes()).hexdigest() for f in O.rglob('*') if f.is_file()}
(O/'binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,compiler_launched=False,solver_launched=False,qualification='Complete native selected declarations and bodies; proof-only private Dot word access, state constructors and harness appended. Adjusted imports, not whole crate/ABI context identity.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files))))
