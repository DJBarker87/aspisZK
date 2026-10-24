"""Exact immutable item inclusion, no implementation edits. --check is read-only."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
R=D.parents[2]
p=R/'crates/aspis-prover/src/state_only_entropy.rs'
s=p.read_text()
def item(start):
 a=s.index(start); b=s.index('{',a); depth=1; end=b+1
 while depth:
  if s[end]=='{':depth+=1
  if s[end]=='}':depth-=1
  end+=1
 return a,end,s[a:end]
spans=[]
a=s.index('const ENTROPY_RETRY_LIMIT:'); b=s.index('\n',a)
spans.append((a,b,s[a:b]))
for marker in ['#[derive(Debug)]\npub enum StateOnlyAttemptEntropyError','impl From<getrandom::Error>','pub struct StateOnlyAttemptSecrets {','#[inline(always)]\nfn entropy_nonzero32','    pub fn generate_for_mask_nonce(']:
 spans.append(item(marker))
sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
text='// Immutable selected source items; see source-map.json.\nuse zeroize::Zeroizing;\n'
text+='\n\n'.join(x[2] for x in spans[:-1])+'\n\nimpl StateOnlyAttemptSecrets {\n'+spans[-1][2]+'\n}\n'
meta=dict(source=str(p.relative_to(R)),source_revision='3e136e21b9ce2576ba4d3385e9e0ab8143bad9b8',source_sha256=sha(s),prefix_through_factory_sha256=sha(s[:spans[-1][1]]),selected_sha256=sha(text),spans=[dict(start_byte=a,end_byte=b,start_line=s[:a].count('\n')+1,end_line=s[:b].count('\n')+1,sha256=sha(t)) for a,b,t in spans],additions=['use zeroize::Zeroizing','enclosing impl StateOnlyAttemptSecrets','test-local include and same-module harness'],omissions='Unreferenced source items and their imports only; no replacement implementations')
for path,data in [(D/'proof/selected.rs',text),(D/'source-map.json',json.dumps(meta,indent=2)+'\n')]:
 if '--check' in sys.argv: assert path.read_text()==data,path
 else:path.write_text(data)
print('exact source association checked' if '--check' in sys.argv else 'exact items generated')
