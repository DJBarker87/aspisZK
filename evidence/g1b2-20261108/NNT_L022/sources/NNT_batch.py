"""Own roots only; retained optimized ledger29 raw ax2 binary, unchanged fixtures."""
from pathlib import Path
import json,subprocess,sys,hashlib,shutil
B=Path.cwd();mode=sys.argv[1].removeprefix('NNT_')
source=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111/NNM_native/NNM_ProofDriver')
binary=source
assert hashlib.sha256(source.read_bytes()).hexdigest()=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
assert hashlib.sha256(binary.read_bytes()).hexdigest()==hashlib.sha256(source.read_bytes()).hexdigest()
(B/'NNT_RAW_BINARY.json').write_text(json.dumps(dict(source=str(source),path=str(binary),sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),bytes=binary.stat().st_size),indent=1)+'\n')
for suffix in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:(B/('NLX_'+suffix)).write_bytes((B/('NNT_'+suffix)).read_bytes())
out=B/'NNT_audit'/sys.argv[1];out.mkdir(parents=True,exist_ok=True)
if mode=='retention':
 exec(compile((B/'NNT_pin.py').read_text(),'NNT_pin.py','exec'));sys.exit(0)
assert mode=='fixtures' or mode.startswith('proof')
with (out/(mode+'.log')).open('w') as f:r=subprocess.run([str(binary),mode],stdout=f,stderr=subprocess.STDOUT)
raw=(out/(mode+'.log')).read_text()
rows=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')]
(out/(mode+'.json')).write_text(json.dumps(dict(exit_status=r.returncode,results=rows),indent=1)+'\n')
print(raw)
if mode.startswith('proof'):
 expected=json.loads((B/'NNT_AUDIT_ROOTS.json').read_text())['groups'][int(mode[5:])]
 assert sorted(x['root'] for x in rows)==sorted(expected)
 assert all(set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in rows)
 assert all(x['equal'] for x in rows)
sys.exit(r.returncode)
