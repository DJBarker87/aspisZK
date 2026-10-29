from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front3b-20261028'
source=json.loads((E/'NDI_SOURCE.json').read_text());pins={}
def add(path,pin):
 h=pin['sha256'] if isinstance(pin,dict) else pin
 if path in pins:assert pins[path]['sha256']==h,('conflicting selected pin',path)
 pins[path]=dict(path=path,sha256=h)
for p in E.glob('NDI_*/receipt.json'):
 x=json.loads(p.read_text())
 for path,pin in x['deps_fingerprint'].get('selected_objects',{}).items():add(path,pin)
for path,pin in json.loads((E/'NDI_EXTRA_PINS.json').read_text())['selected_objects'].items():add(path,pin)
for table in ['tools','coherent_manifests']:
 for path,pin in source['inherited_object_pins'][table].items():add(path,pin)
for path,pin in source['library'].items():add(path,pin)
code='''from pathlib import Path
import json,hashlib
b=Path(B);pins=json.loads(PINS)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
errors=[path for path,pin in pins.items() if sha(path)!=pin['sha256']]
source=json.loads((b/'NDI_SOURCE_PINS.json').read_text());sourceErrors=[p for p,h in source.items() if (b/'NDI_src'/p).is_symlink() or sha(b/'NDI_src'/p)!=h]
print(json.dumps(dict(selected_objects_and_tools=pins,selected_errors=errors,final_source_pins=source,final_source_errors=sourceErrors,audit_object_sha256=sha(b/'NDI_objects/NDI_Audit.olean'),read_only=True)))
'''.replace('Path(B)','Path('+repr(B)+')').replace('json.loads(PINS)','json.loads('+repr(json.dumps(pins))+')')
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);assert not x['selected_errors'] and not x['final_source_errors'],(x['selected_errors'],x['final_source_errors'])
(E/'NDI_FINAL_PINS.json').write_text(json.dumps(x,indent=2)+'\n');print('postflight selected files',len(pins),'private sources',len(x['final_source_pins']))
