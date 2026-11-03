"""Nested-comment-aware source discipline scan for this continuation only."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102'
names=['RetainedMethods','RetainedSpine','RetainedFacts','TrustedStores','OwnedDrain','OwnedPush','RetainedErase','CounterBounds']
def strip(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 assert depth==0
 return ''.join(out)
rows=[]
for n in names:
 p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/('PV_V263_'+n+'.lean')
 s=p.read_text();code=strip(s)
 bad=re.findall(r'\b(?:sorry|axiom|admit|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',code)
 assert not bad,(n,bad)
 rows.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),forbidden_tokens=bad,
 symbolic='list induction, scalar inequalities, small fixed platform/count bounds; no large recurrence or vector evaluation'))
(E/'source-scan-D575.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),comment_stripping='nested Lean block and line comments',files=rows),indent=2)+'\n')
print('Source discipline:',len(rows),'new modules passed')
