from pathlib import Path
import hashlib,json,subprocess,re
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front3b-20261028'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
green={}
for p in sorted(E.glob('NDI_L[0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text());n=x['module']
 if x['exit_status']==0 and n.startswith('NDI_') and n not in ['NDI_TranscriptInspect','NDI_Audit']:
  source=p.parent/'sources'/'NDI_generated'/(n+'.lean')
  current=E/(n+'.lean')
  if current.exists() and current.read_bytes()==source.read_bytes():green[n]=(x,p,source)
expected=[p.relative_to(E).with_suffix('').as_posix() for p in E.glob('*.lean') if p.name not in ['NDI_TranscriptInspect.lean','NDI_Audit.lean']]
for n in expected:assert n in green,('no green source receipt',n)
items=[];theorems=[]
for n,(x,p,s) in sorted(green.items()):
 dest=Path('lean')/(n+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(s.read_bytes())
 printed=[re.search("'([^']+)'",v).group(1) for v in x['print_axioms']]
 for name in re.findall(r'^theorem\s+(\w+)',s.read_text(),re.M):assert any(t.endswith('.'+name) for t in printed),(n,name)
 assert not any('sorryAx' in a for a in x['print_axioms'])
 theorems+=printed;items.append(dict(module=n,source_sha256=sha(s),receipt=str(p.relative_to(E)),receipt_sha256=sha(p),export=str(dest)))
text=''.join('import '+n.replace('/','.')+'\n' for n in sorted(green))+'\n'+''.join('#print axioms '+n+'\n' for n in sorted(set(theorems)))
(E/'NDI_Audit.lean').write_text(text)
(E/'NDI_PROVEN_MODULES.json').write_text(json.dumps(dict(modules=items,theorems=sorted(set(theorems))),indent=2)+'\n')
base=json.loads((E/'NDI_SOURCE.json').read_text())['inherited_object_pins']['selected_objects']
code='''from pathlib import Path
import json,hashlib
b=Path(B);base=json.loads(BASE)
for p in (b/'NDI_objects').rglob('*.olean'):
 if p.name=='NDI_Audit.olean':continue
 base[str(p)]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(dict(selected_objects=base)))
'''.replace('Path(B)','Path('+repr(B)+')').replace('json.loads(BASE)','json.loads('+repr(json.dumps(base))+')')
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'NDI_AUDIT_PINS.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print('green modules',len(items),'top theorem audits',len(set(theorems)))
