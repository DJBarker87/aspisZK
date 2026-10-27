"""Static evidence reconciliation for this job; does not launch any prover."""
from pathlib import Path
import re,json,hashlib,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];valid={};errors=[]
for d in sorted(P.glob('JFz_TX2_[0-9][0-9][0-9]')):
 r=json.loads((d/'receipt.json').read_text());row={k:r[k] for k in ['attempt','sources','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','source_hashes','deps_fingerprint','limits','cgroup','command']}
 assert r['env']['LEAN_PATH'].split(':')[0]=='/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects'
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for src in r['sources']:
  q=d/'sources'/src;assert sha(q)==r['source_hashes'][src]
  if r['exit_status']==0:
   for line in r['print_axioms']:
    if 'depends on axioms:' in line:
     axioms=set(re.search(r'\[([^]]*)\]',line)[1].split(', '));assert axioms<=set(['propext','Classical.choice','Quot.sound']),line
   target=R/'lean'/src
   if target.exists() and sha(target)==sha(q):valid[src]=r['attempt']
 row['receipt_sha256']=sha(d/'receipt.json');rows.append(row)
for p in sorted((R/'lean').glob('JFz_TX2_*.lean')):
 if p.name not in valid:errors.append('No passing current-hash receipt: '+p.name);continue
 s=p.read_text();ns=re.search(r'^namespace (\S+)',s,re.M)
 r=json.loads((P/valid[p.name]/'receipt.json').read_text());prints='\n'.join(r['print_axioms'])
 for ns,body in re.findall(r'^namespace (\S+)\n(.*?)^end \1$',s,re.M|re.S):
  for theorem in re.findall(r'^theorem (\w+)',body,re.M):
   name=ns+'.'+theorem
   if "'"+name+"'" not in prints:errors.append('Missing axiom audit: '+name)
 if re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option (maxHeartbeats|maxRecDepth)',s):errors.append('Forbidden proof form: '+p.name)
result=dict(entry_revision='eb7eab86b9e06595ce4e37a7f20fe44616d845e1',current_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),lean_used=len(rows),lean_limit=100,kani_used=0,kani_limit=10,passed=sum(x['exit_status']==0 for x in rows),rejected=sum(x['exit_status']!=0 for x in rows),wall_seconds=sum(x['wall_seconds'] for x in rows),peak_rss_kib=max(int(x['peak_rss_kib']) for x in rows),swaps=sum(int(x['swaps']) for x in rows),passing_current_sources=valid,errors=errors,attempts=rows)
(P/'JFz_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['lean_used','passed','rejected','wall_seconds','peak_rss_kib','swaps','errors']}))
