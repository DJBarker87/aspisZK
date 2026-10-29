from pathlib import Path
import subprocess,json,hashlib
from NDI_harness import read
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
path='crates/aspis-r1-cost-probe/src/candidate.rs';source=subprocess.check_output(['git','show',F+':'+path],text=True)
helper=read()['crates/aspis-r1-cost-probe/src/NDI_candidate.rs']
def block(s,start):
 begin=s.index('{',start);depth=1;i=begin+1
 while depth:
  if s[i]=='{':depth+=1
  elif s[i]=='}':depth-=1
  i+=1
 return s[begin+1:i-1],begin,i
body,begin,end=block(source,source.index('for j in 0..n {',source.index('fn batch_keys(')))
step,_,_=block(helper,helper.index('fn key_iteration('));assert body.strip()==step.strip()
initial=source[source.index('let mut keys =',source.index('fn batch_keys(')):source.index('for j in 0..n {',source.index('fn batch_keys('))].strip()
init,_,_=block(helper,helper.index('fn key_initial('));assert init.strip()==initial+'\n    keys'
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(E/'NDI_BATCH_SOURCE_ASSOCIATION.json').write_text(json.dumps(dict(frozen_revision=F,source=path,source_sha256=sha(source),step_source_sha256=sha(body.strip()),step_line_start=source[:begin].count('\n')+1,step_line_end=source[:end].count('\n')+1,initialization=initial,capture_map={'queries':'same immutable [u32;22]','lo,n,tree,j':'same usize values; n used for loop bounds only','keys':'local [u64;16] place reborrowed as &mut [u64;16]'},native_helper='NDI_candidate::key_iteration',association='Exact whole loop-body text, not a substring check; no extra native statements. Safe typed reborrow of the same local array; valid bounds exclude panic/overflow. Initialization helper is the exact source prefix plus the return observation. Rust loop desugaring uses Range<usize>::next; separately checked native range packet. No final-array equality is assumed.'),indent=2)+'\n')
print('Whole frozen batch body and initialization match')
