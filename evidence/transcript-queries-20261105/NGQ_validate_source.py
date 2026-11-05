"""Additive NGQ checks; no predecessor validation is relaxed."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
raw=lzma.decompress((E/'NGQ_FROZEN_INPUTS.json.xz').read_bytes());assert sha(raw)==(E/'NGQ_FROZEN_INPUTS.json.sha256').read_text().strip()
fs=json.loads(raw);pins=json.loads((E/'NGQ_FROZEN_SOURCE_PINS.json').read_text());assert set(fs)==set(pins)
for p,t in fs.items():assert sha(t.encode())==pins[p]
assert sha(fs['Cargo.lock'].encode())=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())==next(x['sha256'] for x in json.loads((E/'NGQ_INPUT_PINS.json').read_text())['files'] if x['path'].endswith('KMX_copy_stubs.patch'))
src=fs['crates/aspis-r1-cost-probe/src/transcript.rs'];cuts=json.loads((E/'NGQ_PAIR_CUTS.json').read_text());pairs=(E/'NGQ_pairs_harness.rs.txt').read_text()
def valid_pair(text,k):
 r=cuts[k];body=src[r['source_start']:r['source_end']]
 assert sha(body.encode())==r['sha256']
 m=re.search(rf'fn NGQ_pair{k}\(&self,.*?\{{\n(.*?)\n\(blocks,advances,state\)\n\}}',text,re.S)
 return bool(m and m[1]==body)
assert all(valid_pair(pairs,k) for k in range(8))
controls=[]
for k in range(8):
 bad=pairs.replace(f'blocks[{k}]=self.hash.digest(&[&state,&[1]])',f'blocks[{k}]=self.hash.digest(&[&state,&[3]])',1)
 assert not valid_pair(bad,k);controls.append(dict(stage=k,tag_mutation_rejected=True))
for p in E.glob('*harness.rs.txt'):
 t=p.read_text();assert not re.search(r'\bstatic\b|Option\s*<\s*fn',t),p
assert len(re.findall(r'crate::trace::value\(5,\d+,E::from_m31',src))==22
assert re.findall(r'crate::trace::value\(5,(\d+),E::from_m31',src)==list(map(str,range(22)))
# Add source-fission checks, retaining all earlier predecessor checks.
core=fs['crates/aspis-core/src/r0_transcript.rs']
cut=json.loads((E/'NGQ_SCAN_CUT.json').read_text());word=core[cut['start']:cut['end']]
assert sha(word.encode())==cut['sha256']
assert word in (E/'NGQ_core_harness.rs.txt').read_text()
tail=json.loads((E/'NGQ_TAIL_CUT.json').read_text());native_tail=src[tail['start']:tail['end']]
assert sha(native_tail.encode())==tail['source_sha256']
tail_body=native_tail.replace('aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances)','reply')
assert sha(tail_body.encode())==tail['cut_sha256']
assert tail_body in (E/'NGQ_tail_harness.rs.txt').read_text()
assert [int(x) for x in re.findall(r'crate::trace::value\(5,(\d+),E::from_m31',tail_body)]==list(range(22))
assert 'kani::assume(n<=8192)' in (E/'NGQ_absorb_harness.rs.txt').read_text().replace(' ','')
release=json.loads((E/'NGQ_RELEASE_IDENTITY.json').read_text())
assert release['all_equal'] and release['files_compared']==len(fs)
assert {r['path']:r['sha256'] for r in release['files']}==pins
# The combined theorem must disclose the native trace producer premise.
concrete=(E/'NGQ_Concrete.lean').read_text()
assert '(trace : NGQ_Cuts.Trace hashv' in concrete
assert 'NGQ_Normalize.normalize (NGQ_Effects.code boundaries self row payload)' in concrete
assert 'positions observed.result=positions' in concrete
assert 'observed.attempted=(SdkC_Source.run hashv' in concrete
assert not re.search(r'(?m)^\s*(axiom|opaque)\s|\bsorry\b|\badmit\b|native_decide',concrete)
# Owned branch must not have changed any shipped source file.
assert subprocess.check_output(['git','diff','--name-only','a84229ad238^','--','crates','programs'],text=True)==''
print(json.dumps(dict(source_checks=True,pairs=8,ordered_trace_arguments=22,controls=controls),indent=1))
