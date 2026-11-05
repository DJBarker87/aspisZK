from pathlib import Path
import json,subprocess,time,re
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger11-20261107';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NII_flat'
b={r['module']:r['imports'] for r in map(json.loads,(E/'NII_EXPECTED_IMPORTS.jsonl').read_text().splitlines())};seen=set();todo=['NII_COMBINED_IMPORT']
while todo:
 m=todo.pop()
 if m in seen:continue
 seen.add(m);todo+=b.get(m,[])
configs=json.loads((E/'NII_SUPPLEMENT_CONFIGS.json').read_text());paths={x['prefix']:x['config']['env']['LEAN_PATH'].split(':')for x in configs};
for a in paths:
 d=next(E.parent.glob('*/'+a+'_HANDOFF.md')).parent
 text=(d/(a+'_HANDOFF.md')).read_text()
 paths[a]=re.findall(r'/home/dombarker/project-offloads/[^`\s]*exports[^`\s]*',text)+paths[a]
allpaths=list(dict.fromkeys(p for ps in paths.values()for p in ps));mods=sorted(seen-{'NII_COMBINED_IMPORT'})
code='''from pathlib import Path
import json,hashlib,shutil,subprocess,sys
b=Path(B);c=Path(C)
with (b/'NII_SUPPLEMENT2_barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NII_SUPPLEMENT2_admission.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NII_SUPPLEMENT2_admission.json').read_text());assert r.returncode==0 and a.get('allowed')is True
selected=[str(c),'/home/dombarker/project-offloads/codex-cx-sound-int2-20261025','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']
out=[];missing=[]
for m in modules:
 rel=m.replace('.','/')+'.olean'
 if any(Path(root,rel).is_file()for root in selected):continue
 roots=paths.get(m.split('_')[0],[])+allpaths
 p=next((Path(root,rel)for root in roots if Path(root,rel).is_file()),None)
 if p is None:missing.append(m);continue
 for src in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not src.is_file():continue
  q=c/Path(rel).parent/src.name;q.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(src.read_bytes()).hexdigest()
  assert not q.exists(),('existing supplement',str(q));shutil.copy2(src,q)
  out.append(dict(module=m,source=str(src),destination=str(q),sha256=h,bytes=q.stat().st_size))
(b/'NII_SUPPLEMENT2.json').write_text(json.dumps(dict(files=out,missing=missing,admission=a,exit=r.returncode),indent=1));print(json.dumps(dict(copied=len(out),bytes=sum(x['bytes']for x in out),missing=missing)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\npaths='+repr(paths)+'\nallpaths='+repr(allpaths)+'\nmodules='+repr(mods)+'\n'+code,capture_output=True,text=True)
 (E/f'NII_SUPPLEMENT2_TRANSPORT_{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout[-2500:],r.stderr[-1500:],flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,255]or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for n in ['NII_SUPPLEMENT2.json','NII_SUPPLEMENT2_admission.json','NII_SUPPLEMENT2_barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
