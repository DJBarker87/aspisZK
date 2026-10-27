from pathlib import Path
import json,subprocess,shlex
P=Path(__file__).resolve().parent;root='/home/dombarker/project-offloads/aspis-joint-20261019/objects/'
mods=[c['module'] for c in json.loads((P/'checks.json').read_text())]
assert all(m.startswith('PV_Ledger_Recount5_') and m.replace('_','').isalnum() for m in mods)
paths=[root+m+suffix for m in mods for suffix in ['.olean','.ilean','.trace']]
script='python3 -c '+shlex.quote('import os,json,hashlib; p='+repr(paths)+'; found=[dict(path=f,sha256=hashlib.sha256(open(f,"rb").read()).hexdigest(),size=os.path.getsize(f)) for f in p if os.path.isfile(f)]; [os.unlink(x["path"]) for x in found]; print(json.dumps(dict(removed=found,rule="Only this job newly named helper objects; sources and all other objects retained")))')
r=subprocess.run(['ssh','dombarker@100.108.41.90',script],capture_output=True);assert r.returncode==0,r.stderr
(P/'helper-object-cleanup5.json').write_bytes(r.stdout)
print('Own helper object cleanup recorded')
