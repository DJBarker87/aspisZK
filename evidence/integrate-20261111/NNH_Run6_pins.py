"""Pin only explicit own outputs read-only; never copy or traverse caches."""
from pathlib import Path
import subprocess,json,hashlib,time,sys
E=Path(__file__).resolve().parent
selected={}
for p in sorted(E.glob('NNH_L9[0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if int(r['attempt'][-3:])<907 or r['exit_status']!=0:continue
 cmd=r['command'];out=cmd[cmd.index('-o')+1] if '-o' in cmd else None
 if out:selected[out]={'attempt':r['attempt'],'module':r['module'],'source_revision':r['source_revision'],'source_hashes':r['source_hashes']}
code='''from pathlib import Path
import json,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-integrate-20261111')
selected=json.loads(INPUT)
for rel,entry in selected.items():
 p=B/rel
 assert p.is_file(), str(p)
 entry['objects']={}
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():entry['objects'][str(z)]={'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'bytes':z.stat().st_size}
print(json.dumps(selected))
'''.replace('INPUT',repr(json.dumps(selected)))
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with (E/'NNH_Run6_PIN_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps({'phase':sys.argv[1],'retry':retry,'exit':r.returncode,'stderr':r.stderr})+'\n')
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
(E/('NNH_Run6_OBJECTS_'+sys.argv[1]+'.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'phase':sys.argv[1],'modules':len(out),'objects':sum(len(v['objects']) for v in out.values())}))
