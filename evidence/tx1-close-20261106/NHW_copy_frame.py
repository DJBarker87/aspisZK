"""Check literal source fission and retain KMX theorem provenance."""
from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
s=subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/candidate.rs']).decode()
assert 'let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();' in s
h=(E/'NHW_window.rs.txt').read_text();assert 'let folded_root: [u8;32]=proof[start..start+32].try_into().unwrap();' in h
assert not re.search(r'\b(static|stub_verified|proof_for_contract)\b|Option\s*<\s*fn',h)
kmx='evidence/kani-reverify1-20261028/KMX_CopyMeaning.lean'
raw=subprocess.check_output(['git','show','HEAD:'+kmx]);adapt=raw.decode()
(E/'NHW_COPY_PROVENANCE.json').write_text(json.dumps(dict(frozen_revision=rev,source_sha256=hashlib.sha256(s.encode()).hexdigest(),harness_sha256=hashlib.sha256(h.encode()).hexdigest(),kmx_source=kmx,kmx_sha256=hashlib.sha256(raw).hexdigest(),adaptation='reuse existing imported KMX_CopyMeaning unchanged; no duplicated proof or copy-stub change',cut='literal 32-byte try_into expression; slice selection factored to an arbitrary offset'),indent=1)+'\n')
