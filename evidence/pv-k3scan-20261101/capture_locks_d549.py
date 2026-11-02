from pathlib import Path
import subprocess,json,hashlib,lzma,time
E=Path(__file__).resolve().parent
roots=sorted({json.loads(p.read_text()).get('source_root',json.loads(p.read_text())['package'])for p in E.glob('config-K792*.json')})
code="""from pathlib import Path
import json,hashlib,time
R=Path('/home/dombarker/project-offloads/codex-pv-k3scan-20261101')
roots=ROOTS
out={'epoch':time.time(),'locks':[]}
for root in roots:
 for p in (R/root).rglob('Cargo.lock'):
  if 'target' in p.parts:continue
  out['locks'].append({'source_root':root,'relative':str(p.relative_to(R/root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'text':p.read_text()})
p=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json');out['quiet_window']={'exists':p.exists(),'text':p.read_text()if p.exists()else None}
print(json.dumps(out))
""".replace('ROOTS',repr(roots))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
d=json.loads(r.stdout);checked=[]
for p in (E/'host').glob('K792*/receipt.json'):
 rec=json.loads(p.read_text());cfg=rec.get('config',{});root=cfg.get('source_root',cfg.get('package'));invp=p.parent/'source-sha256.json'
 if not root or not invp.exists():continue
 inv=json.loads(invp.read_text())
 for x in d['locks']:
  if x['source_root']==root and x['relative']in inv:
   assert inv[x['relative']]==x['sha256'],(p,x['relative']);checked.append({'run':p.parent.name,'source_root':root,'path':x['relative'],'sha256':x['sha256']})
d['receipt_hash_matches']=checked;raw=(json.dumps(d,indent=2)+'\n').encode();(E/'D549-LOCKS.json.xz').write_bytes(lzma.compress(raw));(E/'D549-LOCKS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');print({'roots':len(roots),'locks':len(d['locks']),'matches':len(checked),'quiet_window':d['quiet_window']})
