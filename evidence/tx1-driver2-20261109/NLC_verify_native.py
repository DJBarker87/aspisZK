from pathlib import Path
import re,json,hashlib
B=Path(__file__).resolve().parent;S=B/'NLC_src';sha=lambda b:hashlib.sha256(b).hexdigest()
frozen=(B/'NLC_FROZEN_SEMANTIC.rs.txt').read_text();helper=(S/'crates/aspis-r1-cost-probe/src/NLC_native.rs').read_text()
def block(s,start):
 a=s.index('{',start);depth=0
 for j in range(a,len(s)):
  if s[j]=='{':depth+=1
  if s[j]=='}':
   depth-=1
   if not depth:return s[a:j+1]
 raise AssertionError('Unbalanced source block')
a=block(frozen,frozen.index('Ok(Verified {',frozen.index('fn verify_finish')))
a=re.sub(r'\s*#\[cfg\(feature = "prover"\)\]\s*\w+,','',a)
a=a.replace('*prefix.c1_root','*c1_root').replace('prefix.payload(2)?.try_into().unwrap()','root')
b=block(helper,helper.index('    Verified {',helper.index('fn source_construct')))
norm=lambda s:re.sub(r'\s+','',s)
assert norm(a)==norm(b),'Constructor source mismatch'
assert '.map_err(|_|Error::Public)' in norm(frozen)
assert 'terminal.map_err(|_|Error::Public)' in norm(helper)
checks=[]
for i in range(1,21):
 n=f'NLC_K{i:03}';g=json.loads((B/(n+'-graph-check.json')).read_text());l=json.loads((B/(n+'-lock-check.json')).read_text());assert g['graph_matches_frozen'] and l['unchanged']
 assert all('prover' not in p['features'] and 'cu-profiling' not in p['features'] for p in g['selected_closure'])
 checks.append(dict(attempt=n,graph_sha256=g['graph_sha256'],lock_unchanged=True,features_checked=True))
out=dict(source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_file_sha256=sha(frozen.encode()),constructor_normalized_sha256=sha(norm(a).encode()),constructor_body_matches=True,map_expression_matches=True,substitutions=['prefix.c1_root projected to borrowed c1_root','payload conversion completes before constructor window; carried root supplied','prover-only fields excluded by recorded deployed feature set'],native_domain='constructor helper Hash(u64), digest unreachable; no generic/deployed carrier transport claimed',native_installed_as_whole_parent=False,attempts=checks)
(B/'NLC_NATIVE_SOURCE_REVIEW.json').write_text(json.dumps(out,indent=2));print('Source spans,20 frozen graphs/locks and deployed features validated; constructor type transport remains OPEN')
