#!/usr/bin/env python3
"""Same native input/cut domain, on-demand dot replies replacing the indexed ghost tape."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;O=Path(sys.argv[1])
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-claim-20261025/prepare.py'),'--out',str(O),'--halves'],check=True)
p=O/'min/src/prepared_claim_native/proofs.rs';s=p.read_text();changes=[
('static mut DOT_WORDS:[[u64;8];174]=[[0;8];174];','static mut DOT_LAST:[u64;8]=[0;8];'),
('static mut DOT_COUNTS:[usize;174]=[0;174];','static mut DOT_COUNT_LAST:usize=0;'),
('DOT_WORDS[n-1][i]','DOT_LAST[i]'),('DOT_COUNTS[n-1]','DOT_COUNT_LAST'),
('*dot=crate::fast_pairing::EbyKDot::proof_input(DOT_WORDS[n],DOT_COUNTS[n]);CPUSH=n+1;',
 'let words=kani::any::<[u64;8]>();let count=kani::any::<usize>();*dot=crate::fast_pairing::EbyKDot::proof_input(words,count);DOT_LAST=words;DOT_COUNT_LAST=count;CPUSH=n+1;'),
('DOT_WORDS[29*p+28][i]','DOT_LAST[i]'),('DOT_COUNTS[29*p+28]','DOT_COUNT_LAST'),
('DOT_WORDS=kani::any();DOT_COUNTS=kani::any();','DOT_LAST=[0;8];DOT_COUNT_LAST=0;')]
for a,b in changes:
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
assert 'DOT_WORDS'not in s and 'DOT_COUNTS'not in s and 'kani::assume'not in s and 'transmute'not in s
p.write_text(s);(T/'proofs.rs').write_text(s)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest()for p in O.rglob('*')if p.is_file()}
(O/'stream-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,changes=changes,domain='Identical canonical native semantic/E inputs, arbitrary928-byte y1, nine primitive normal-return cuts. Every reached push still receives an independent arbitrary full native eight-u64/count state; only ghost reply storage/indexing changes.',trace_transport='For any original174-entry tape use its n-th state as the n-th reached fresh reply. For any reached streamed prefix of at most174 pushes, extend it arbitrarily to a174-entry tape. Each comparison reads only the immediately preceding reached reply, or zero at a new row; finish reads its own29th reply. Unreached replies are unobserved. No distribution/security equality is claimed.',remaining='Kani still required; native primitive/effect/SDK/runtime/extraction/oracle/release joins unchanged. Historical25866 component, not whole4bb3.'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY',files=len(files),native_changes=False,normal_return_cuts=9)))
