"""Retain only current-source accepted own objects; never claim cb3 provenance."""
from pathlib import Path
import json,subprocess,shlex
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
status=json.loads((out/'proof-status.json').read_text());assert all(x['status']=='accepted' for x in status['modules'])
code='''from pathlib import Path
import json,hashlib,shutil
base=Path('/home/dombarker/project-offloads/codex-pv-cblib-20261027');shared=Path('/home/dombarker/project-offloads/aspis-joint-20261019');rows=[]
for row in %r:
 module=row['module'];src=shared/'sources'/(module+'.lean');obj=shared/'objects'/(module+'.olean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==row['sha256'],module
 h=hashlib.sha256(obj.read_bytes()).hexdigest();dest=base/'lean-objects'/(module+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(obj,dest);assert hashlib.sha256(dest.read_bytes()).hexdigest()==h
 rows.append({'module':module,'source_sha256':row['sha256'],'object_sha256':h,'copied_from':str(obj),'destination':str(dest),'focused_receipt':row['receipt']})
print(json.dumps({'requested_cb3_cache_exists':Path('/home/dombarker/project-offloads/codex-pv-cb3-20261026/lean-objects').exists(),'cb3_binaries_copied':False,'scope':'current-source accepted own objects copied from shared Env-J; cached dependency closure/release association is not newly certified','objects':rows},indent=2))'''%status['modules']
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True,check=True)
(out/'retained-own-cache.json').write_text(p.stdout);print(len(status['modules']),'accepted own objects retained')
