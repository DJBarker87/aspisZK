from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front3b-20261028'
base=json.loads((E/'NDI_SOURCE.json').read_text())['inherited_object_pins']['selected_objects']
code='''from pathlib import Path
import json,hashlib
b=Path(B);c=b.parent/'codex-cx-sound-int2-20261025';manifest=c/'final-closure-manifest.json';m=json.loads(manifest.read_text())['modules'];base=json.loads(BASE)
roots=[b/'NDI_objects',b.parent/'codex-cx-native-front3-20261028/NDF_objects',b.parent/'codex-cx-front3-cache-20261028/NCO_objects',b.parent/'codex-cx-front3-cache-20261028',c,c/'objects']
selected={};seen=set();overrides=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def visit(name):
 if name in seen:return
 seen.add(name);v=m[name];relative=Path(name.replace('.','/')+'.olean')
 p=next((root/relative for root in roots if (root/relative).is_file()),Path(v['path']))
 h=sha(p)
 if h!=v['sha256']:
  assert str(p) in base and base[str(p)]['sha256']==h,('unreviewed coherent override',name,str(p),h,v['sha256'])
  overrides.append(dict(module=name,selected=h,coherent=v['sha256'],inherited_override=True))
 selected[str(p)]=dict(path=str(p),sha256=h,bytes=p.stat().st_size)
 for dep in v['imports']:visit(dep)
visit('R1SemanticPublicCodecComplete')
print(json.dumps(dict(root='R1SemanticPublicCodecComplete',selected_objects=selected,modules=len(seen),inherited_overrides=overrides,coherent_manifest_sha256=sha(manifest))))
'''.replace('Path(B)','Path('+repr(B)+')').replace('json.loads(BASE)','json.loads('+repr(json.dumps(base))+')')
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);(E/'NDI_EXTRA_PINS.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
(E/'NDI_EXTRA_PINS.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n');print('extra coherent closure pinned',json.loads(r.stdout)['modules'])
