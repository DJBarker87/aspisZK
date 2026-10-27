"""Resolve final source-law import closure under h4, h5 and h5'. Read-only."""
from pathlib import Path
import json,hashlib,re,subprocess,shlex
E=Path('evidence/pv-batch2-20261027/batch2e');C=E.parent/'batch2c';L=Path('docs/research/v8-r0-zk-20261009/lean')
def show(rev,p):return subprocess.check_output(['git','show',rev+':'+p])
inv=json.loads(show('research','evidence/envj-rebuild-20261026/EJR_final-inventory.json'));ejr={a['module']:a['resolution'] for a in inv['selected'] if a.get('resolution')}
freeze=json.loads(show('research','docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json'));fr={a['module'].replace('.','/'):a for a in freeze['sources']}
ext={r['module'] for r in json.loads((C/'external-object-manifest.json').read_text())}
h5=json.loads((C/'H5-SOURCE-PINS.json').read_text());own={}
for a in json.loads((C/'AUDIT-PREFLIGHT.json').read_text())['accepted']:own[a['module']]=str(L/(a['module']+'.lean'))
for p in list((L/'R1Z').glob('PV_B2_D_*.lean'))+list((L/'R1Z').glob('PV_B2_E_*.lean')):own['R1Z/'+p.stem]=str(p)
for m,r in h5.items():own[m]=r['path']
seen=set();rows=[];missing=[];order=[]
def visit(m):
 m=m.replace('.','/')
 if m in seen:return
 seen.add(m)
 if m in ext:return
 if m in ejr:p=ejr[m]['path'];b=show('research',p);authority='EJR';blob=ejr[m]['blob']
 elif m in fr:p=fr[m]['path'];b=show('research',p);assert hashlib.sha256(b).hexdigest()==fr[m]['sha256'];authority='freeze';blob=None
 elif m in own:
  p=own[m];b=Path(p).read_bytes();authority='own PV source' if m.split('/')[-1].startswith('PV_B2_') else 'h5 own HEAD';blob=None
  r=subprocess.run(['git','rev-parse','HEAD:'+p],capture_output=True,text=True)
  if r.returncode==0:blob=r.stdout.strip()
  if authority=='h5 own HEAD':assert b==show('HEAD',p)
 else:missing.append(m);return
 row=dict(module=m,path=p,authority=authority,git_blob=blob,sha256=hashlib.sha256(b).hexdigest())
 if m in own and authority in ['EJR','freeze']:
  tracked=Path(own[m]).read_bytes();row['own_tracked_sha256']=hashlib.sha256(tracked).hexdigest();row['h5_prime_resolution']='EJR/freeze wins'
 rows.append(row)
 s=b.decode();s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
 for line in re.findall(r'^import ([^\n]+)',s,re.M):
  for i in line.split('--')[0].split():visit(i)
 order.append(m)
for m in own:visit(m)
assert not missing,missing
code='''import sys,json,hashlib
from pathlib import Path
rows=json.load(sys.stdin)
for a in rows:
 if a['authority'] not in ['EJR','freeze']:continue
 p=Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources')/(a['module']+'.lean')
 a['host_sha256']=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
 a['host_source_matches']=a['host_sha256']==a['sha256']
print(json.dumps(rows))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(rows),text=True,capture_output=True,check=True);rows=json.loads(r.stdout)
bad=[r for r in rows if r.get('host_source_matches') is False]
(E/'PROJECT-CLOSURE.json').write_text(json.dumps(dict(rows=rows,topological_order=order,unresolved=missing,shared_source_mismatches=bad),indent=2)+'\n');assert not bad,bad
(E/'H5-SOURCE-PINS.json').write_text(json.dumps({r['module']:dict(module=r['module'],path=r['path'],git_blob=r['git_blob'],sha256=r['sha256'],authority=r['authority']) for r in rows if r['authority']=='h5 own HEAD'},indent=2)+'\n')
print('project closure',len(rows),'sources; no missing or changed shared source')
