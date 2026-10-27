"""Resolve sampler imports only through permitted project and library authorities."""
from pathlib import Path
import subprocess,json,re,hashlib,shlex,sys
E=Path('evidence/pv-batch2-20261027/batch2c')
def show(p):return subprocess.check_output(['git','show','research:'+p])
def strip_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif not depth and s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:
   out.append(s[i] if not depth or s[i]=='\n' else ' ');i+=1
 return ''.join(out)
inv=json.loads(show('evidence/envj-rebuild-20261026/EJR_final-inventory.json'));lookup={a['module']:a for a in inv['selected']}
freeze=json.loads(show('docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json'));fr={a['module'].replace('.','/'):a for a in freeze['sources']}
lib={a['module'] for a in json.loads((E/'external-object-manifest.json').read_text())}
queue=json.loads((E/'SAMPLER-PREFLIGHT.json').read_text())['external_imports']
if '--gamma' in sys.argv:queue+=['AspisR1Post25SamplerIndexedAddSmallCandidate.Funs','IndexedCandidateAddSmallWrapperNatModelV3','GammaCandidateAddSmallHelpersRefine']
seen=set();rows=[];missing=[]
while queue:
 m=queue.pop().replace('.','/')
 if m in seen:continue
 seen.add(m)
 if m in lib:continue
 a=lookup.get(m);resolution=a.get('resolution') if a else None
 if resolution:p=resolution['path'];authority='EJR_final-inventory.json';blob=resolution['blob']
 elif m in fr:p=fr[m]['path'];authority='prover-commit47/final-source-freeze.json';blob=None
 else:missing.append(m);continue
 try:b=show(p)
 except subprocess.CalledProcessError:missing.append(m+' recorded source absent at research:'+p);continue
 sha=hashlib.sha256(b).hexdigest()
 if m in fr and not resolution:assert sha==fr[m]['sha256']
 rows.append(dict(module=m,resolution_path=p,source_sha256=sha,authority=authority,recorded_blob=blob))
 for line in re.findall(r'^import ([^\n]+)',strip_comments(b.decode()),re.M):queue.extend(line.split('--')[0].split())
code='''import json,hashlib,sys
from pathlib import Path
rows=json.load(sys.stdin)
for a in rows:
 p=Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources')/(a['module']+'.lean')
 a['shared_source_path']=str(p);a['shared_source_sha256']=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
 a['matches_research']=a['shared_source_sha256']==a['source_sha256']
print(json.dumps(rows))
'''
if '--offline' in sys.argv:
 out=E/('GAMMA-IMPORT-SOURCE-PREFLIGHT.json' if '--gamma' in sys.argv else 'SAMPLER-IMPORT-SOURCE-PREFLIGHT.json')
 out.write_text(json.dumps(dict(modules=len(seen),project_modules=rows,unresolved=missing,host_source_check='PENDING; no host compile authorized by this offline record'),indent=2)+'\n');print('offline closure',len(seen),'projects',len(rows),'missing',missing);raise SystemExit(bool(missing))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(rows),capture_output=True,text=True,check=True);rows=json.loads(r.stdout)
bad=[a for a in rows if not a['matches_research']]
j=dict(modules=len(seen),project_modules=rows,unresolved=missing,shared_source_mismatches=bad,passed=not missing and not bad,no_shared_writes=True)
(E/('GAMMA-IMPORT-CLOSURE.json' if '--gamma' in sys.argv else 'SAMPLER-IMPORT-CLOSURE.json')).write_text(json.dumps(j,indent=2)+'\n');print('closure',len(seen),'projects',len(rows),'missing',missing,'mismatch',bad)
if missing or bad:raise SystemExit(1)
