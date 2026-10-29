from pathlib import Path
import json,lzma,subprocess,hashlib
D=Path(__file__).resolve().parent
j=json.load(open(D/'rebuild-input.json'));tr=json.load(lzma.open(D.parent/'pv-mfb-20261029/exact-traces.json.xz'));ext={v['module'].replace('/','.') for v in json.load(open(D.parent/'pv-mfb-20261029/external-object-manifest.json'))};base={k.replace('/','.') for k in json.load(open(D.parent/'pv-mfb-20261029/dlib-preflight-input.json'))['source_closure']}
jobs=[]
for rid in ['V260','V195','V219','V246','V261']:
 r=next(x for x in tr if x['id']==rid);mods=r['modules'];seen=set()
 def walk(m):
  if m in seen or m in ext or m in base or m in j['modules']:return
  seen.add(m);v=mods[m]
  for dep in v['imports']:walk(dep)
  raw=subprocess.check_output(['git','show','HEAD:'+v['path']]);assert hashlib.sha256(raw).hexdigest()==v['sha256']
  j['modules'][m]=v;p=D/'sources'/(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw);jobs.append(['rebuild',m])
 walk(r['closing']['module']);j['rows'][rid]=r['closing'];jobs.append(['check',rid])
(D/'next-input.json').write_text(json.dumps(j,indent=2)+'\n');(D/'next-jobs.json').write_text(json.dumps(jobs,indent=2)+'\n')
print(len(jobs),'focused jobs; admit at most remaining 69')
