from pathlib import Path
import subprocess,json,base64,lzma,hashlib
E=Path(__file__).resolve().parent
code=r'''from pathlib import Path
import json,base64
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata2-20261104')
names=['NFR_C_EXTRACTION_PINS.json','NFR_C_helper.llbc','NFR_C_ref/Cargo.lock']+[str(p.relative_to(b)) for p in (b/'NFR_C_helper_extracted').rglob('*') if p.is_file()]
print(json.dumps({n:base64.b64encode((b/n).read_bytes()).decode() for n in names}))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
D=E/'NFR_C_E001_outputs';D.mkdir(exist_ok=True);manifest=[]
for n,s in json.loads(r.stdout).items():
 raw=base64.b64decode(s);p=D/(n.replace('/','__')+('.txt' if n.endswith('.lean') else ''))
 if n.endswith('.llbc') or len(raw)>20_000_000:
  p=Path(str(p)+'.xz');p.write_bytes(lzma.compress(raw,preset=6));Path(str(p).removesuffix('.xz')+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:p.write_bytes(raw)
 manifest.append(dict(host_path=n,stored=str(p.relative_to(E)),sha256=hashlib.sha256(raw).hexdigest(),size=len(raw)))
(E/'NFR_C_EXTRACTION_MANIFEST.json').write_text(json.dumps(manifest,indent=1)+'\n')
print('Retained',len(manifest),'extraction outputs; external template is excluded text, never a compiled axiom module')
