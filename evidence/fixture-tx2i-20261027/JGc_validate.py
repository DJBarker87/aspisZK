"""Static exact-source/receipt/axiom inventory. No theorem replay."""
from pathlib import Path
import json,hashlib,re,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
receipts=[];accepted={}
for f in sorted(P.glob('JGc_TX2_*/receipt.json')):
 r=json.loads(f.read_text());r['receipt_path']=str(f.relative_to(R));receipts.append(r)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},f
 assert '-M7000' in r['command'],f
 assert r['env']['LEAN_PATH'].split(':')[0]=='/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects',f
 if r['exit_status']!=0:continue
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  if 'axioms: [' in line:
   names={v.strip() for v in line.split('axioms: [')[1].rstrip(']').split(',') if v.strip()}
   assert names<={'propext','Classical.choice','Quot.sound'},line
 for name,sha in r['source_hashes'].items():accepted[(name,sha)]=r
modules=[];unchecked=[]
for f in sorted((R/'lean').glob('JGc_*.lean')):
 text=f.read_text();sha=hashlib.sha256(f.read_bytes()).hexdigest()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',text),f
 r=accepted.get((f.name,sha))
 if r is None:unchecked.append(str(f.relative_to(R)));continue
 theorem_names=re.findall(r'^theorem\s+([\w\']+)',text,re.M)
 for name in theorem_names:
  assert re.search(r'#print axioms\s+'+re.escape(name)+r'\b',text), (f,name)
  assert any('.'+name+"' " in line for line in r['print_axioms']), (f,name,'missing receipt axiom')
 modules.append(dict(module=f.stem,sha256=sha,receipt=r['receipt_path'],theorems=len(theorem_names)))
out=dict(attempts=len(receipts),passed=sum(r['exit_status']==0 for r in receipts),rejected=sum(r['exit_status']!=0 for r in receipts),kani_runs=0,total_wall_seconds=sum(r['wall_seconds'] for r in receipts),maximum_rss_kib=max([int(r['peak_rss_kib']) for r in receipts] or [0]),swaps=sum(int(r['swaps']) for r in receipts),modules=modules,unchecked=unchecked)
assert len(receipts)<=100
(P/'JGc_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['modules','unchecked']});print('checked modules',len(modules),'unchecked modules',len(unchecked))
if '--final' in sys.argv:assert not unchecked,unchecked
