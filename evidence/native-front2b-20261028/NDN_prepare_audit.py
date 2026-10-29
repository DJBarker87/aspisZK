from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
mods={'NDN_PackedReference':57,'NDN_PackedFrame':14,'NDN_AddWordBridge':59,'NDN_CoordinateBridge':60,'NDN_ArithmeticBounds':66,'NDN_SerializationBridge':67,'NDN_BindingBoolean':73,'NDN_FieldAppendInduction':74,'NDN_RawProductBridge':70,'NDN_InterpolationBridge':71,'NDN_InterpolationPrestate':75,'NDN_InterpolationPrefix':79,'NDN_RequestTagFinding':76}
s='\n'.join('import '+m for m in mods)+'\n'
accepted=[]
for m,n in mods.items():
 p=E/(m+'.lean');r=json.loads((E/f'NDN_L{n:03}/receipt.json').read_text());assert r['exit_status']==0
 sh=hashlib.sha256(p.read_bytes()).hexdigest();assert r['source_hashes']['NDN_generated/'+m+'.lean']==sh,(m,'passing source differs')
 stack=[]
 for line in p.read_text().splitlines():
  line=line.strip()
  if line.startswith('namespace '):stack.append(line.split()[1])
  elif line=='noncomputable section' or line.startswith('section'):stack.append(None)
  elif line=='end' or line.startswith('end '):
   if stack:stack.pop()
  elif line.startswith('#print axioms '):
   name=line.removeprefix('#print axioms ')
   if not name.startswith(('AspisR1.','NDN_')):name='.'.join(x for x in stack if x)+'.'+name
   s+='#print axioms '+name+'\n';accepted.append(dict(theorem=name,module=m,attempt=f'NDN_L{n:03}',source_sha256=sh))
(E/'NDN_Audit.lean').write_text(s)
(E/'NDN_ACCEPTED_MODULES.json').write_text(json.dumps(dict(modules=mods,theorems=accepted,excluded=['NDN_EqualityLoop (L077 failed alias rewrites)','NDN_ChunkGeometry (L078 parser failure)'],header_warning='NDN_RequestTagFinding only proves the BAD E015 reference accepts tag zero; no source association is claimed.'),indent=2)+'\n')
code="""from pathlib import Path
import hashlib,json
b=Path('/home/dombarker/project-offloads/codex-cx-native-front2b-20261028/NDN_objects')
print(json.dumps({str(p):dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in b.rglob('*.olean')}))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
pins=json.loads((E/'NDN_COHORT_PINS.json').read_text());pins.update(json.loads(r.stdout));pins.update({n:dict(path=n,sha256=h) for n,h in json.loads((E/'NDN_SOURCE.json').read_text())['library'].items()})
(E/'NDN_AUDIT_PINS.json').write_text(json.dumps(dict(selected_objects=pins),indent=2)+'\n')
print(len(accepted),'audited theorem names;',len(pins),'selected objects pinned')
