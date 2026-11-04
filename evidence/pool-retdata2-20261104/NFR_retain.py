"""Copy current successful lane objects into the retained own cache; never delete."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
modules=json.loads((E/'NFR_AUDIT_INPUTS.json').read_text())['modules']+['NFR_WALKER','NFR_MemoryLimit','NFR_Driver','NFR_Coherence']
code=f'''from pathlib import Path
import shutil,json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata2-20261104')
cache=b.parent/'codex-cx-pool-retdata2-cache-20261104'
objects=cache/'NFR_final_objects_20261104';objects.mkdir(exist_ok=True)
native=cache/'NFR_audit_native_20261104';native.mkdir(exist_ok=True)
pins=[]
for module in {modules!r}:
 rel=module.replace('.','/')
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  source=next((root/(rel+suffix) for root in [b/'NFR_B_objects',b/'NFR_C_objects'] if (root/(rel+suffix)).exists()),None)
  if source:
   dest=objects/(rel+suffix);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,dest)
   pins.append(dict(source=str(source),path=str(dest),sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),size=dest.stat().st_size))
 source=next((root/(rel+'.lean') for root in [b/'NFR_B_generated',b/'NFR_C_generated'] if (root/(rel+'.lean')).exists()),None)
 assert source,module+' missing successful source'
 dest=objects/(rel+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,dest)
 pins.append(dict(source=str(source),path=str(dest),sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),size=dest.stat().st_size))
for name in ['NFR_Driver','NFR_Coherence','NFR_Driver.c','NFR_Coherence.c','NFR_WALKER.c','NFR_MemoryLimit.c']:
 source=b/'NFO_native'/name;dest=native/name;assert source.exists();shutil.copy2(source,dest)
 pins.append(dict(source=str(source),path=str(dest),sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),size=dest.stat().st_size))
print(json.dumps(dict(cache=str(cache),objects=str(objects),native=str(native),pins=pins),sort_keys=True))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code.encode(),capture_output=True)
assert r.returncode==0,r.stderr
result=json.loads(r.stdout);result.update(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),proof_modules=modules,classification='Copies of successful current objects/source/sidecars and native audit executables; no imported cache modified; no own cache deleted',audit='NFR_AUDIT.json',input_manifest='NFR_AUDIT_INPUTS.json')
(E/'NFR_RETAINED.json').write_text(json.dumps(result,indent=1)+'\n')
print('Retained',len(result['pins']),'source/object/sidecar/audit files')
