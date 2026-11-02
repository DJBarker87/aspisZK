"""D564: audit code tokens, ignoring nested Lean comments; summary-based lists only."""
from pathlib import Path
import json,re,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin73-20261102'

def code_without_comments(source):
 out=[];i=0;depth=0
 while i<len(source):
  pair=source[i:i+2]
  if pair=='/-':depth+=1;i+=2;continue
  if depth and pair=='-/':depth-=1;i+=2;continue
  if depth:i+=1;continue
  if pair=='--':
   end=source.find('\n',i);i=len(source) if end<0 else end;continue
  out.append(source[i]);i+=1
 assert depth==0,'unterminated comment'
 return ''.join(out)

rec=[v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())];checks=[]
for v in rec:
 if not v['accepted']:continue
 p=Path(v['source']['path']);b=subprocess.check_output(['git','show','HEAD:'+str(p)],cwd=R)
 assert hashlib.sha256(b).hexdigest()==v['source_sha256'],v['module']
 s=code_without_comments((R/p).read_text())
 hits=[x for x in ['sorry','native_decide','axiom','set_option maxHeartbeats','set_option maxRecDepth'] if re.search(r'\b'+re.escape(x)+r'\b',s)]
 assert not hits,(str(p),hits)
 for a in v['axioms']:
  if 'depends on axioms:' in a:
   axs=re.search(r'\[([^]]*)\]',a).group(1)
   assert set(x.strip() for x in axs.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},(v['module'],a)
 checks.append(dict(module=v['module'],sha256=v['source_sha256'],source_revision=v['source_revision'],standard_axioms_only=True,source_hash_match=True))
(E/'accepted-source-audit-D564.json').write_text(json.dumps(checks,indent=2)+'\n')
print('Accepted source/axiom checks:',len(checks))
