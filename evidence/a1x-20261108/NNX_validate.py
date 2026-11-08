from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
rs=[];errors=[]
for p in sorted(E.glob('NNX_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());rs.append(r);a=r['attempt']
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert r['timeout']==180 and r['swaps']=='0',a
 for n,h in r['source_hashes'].items():assert hashlib.sha256((E/a/'sources'/n).read_bytes()).hexdigest()==h,(a,n)
 for line in r.get('print_axioms',[]) if r['exit_status']==0 else []:
  assert 'sorryAx' not in line and ('axioms: [' in line or 'does not depend on any axioms' in line),(a,line)
  if 'axioms: [' in line:
   names=line.split('axioms: [',1)[1].split(']',1)[0].split(', ')
   assert set(names)<=set(['propext','Classical.choice','Quot.sound']), (a,names)
 assert any(Path(x).name=='Aeneas.olean' for x in r['deps_fingerprint']['selected_objects']),a
 assert 'NNX_objects' in r['env']['LEAN_PATH'].split(':')[0],a
events=[json.loads(l) for l in (E/'NNX_ATTEMPTS.jsonl').read_text().splitlines()]
for r in rs:
 a=r['attempt'];shares=[e for e in events if e.get('attempt')==a and e.get('event')=='share_check']
 assert shares and shares[-1]['host']['count']<6,a
 disks=list(E.glob(a+'-disk-*.json'));assert disks and json.loads(sorted(disks)[-1].read_text())['free']>=40_000_000_000,a
latest={}
for r in rs:
 if r['exit_status']==0:latest[r['module']]=r
accepted=[]
for module,r in latest.items():
 p=E/(module+'.lean')
 if not p.exists():continue
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert h in r['source_hashes'].values(),module
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',p.read_text()),module
 accepted.append(module)
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
result=dict(scopes=len(rs),passes=sum(r['exit_status']==0 for r in rs),failures=sum(r['exit_status']!=0 for r in rs),accepted_current_modules=sorted(accepted),budget=50,exhausted=len(rs)==50,target_established=False,checks='admission, limits, timeout, swap, source snapshots, accepted source hashes, printed standard axioms, Aeneas direct pins, overlay order, file sizes')
(E/'NNX_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
