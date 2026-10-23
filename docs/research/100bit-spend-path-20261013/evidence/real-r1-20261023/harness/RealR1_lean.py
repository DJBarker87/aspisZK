#!/usr/bin/env python3
"""One assigned focused host compile; retain every attempt, including errors."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

module, attempt = sys.argv[1:]
assert module.startswith('R1Z.RealR1_') and 10900 <= int(attempt) <= 10999
root = Path(__file__).resolve().parent.parent
rel = module.replace('.', '/') + '.lean'
source = Path('docs/research/v8-r0-zk-20261009/lean') / rel
receipt = root / 'lean' / attempt
receipt.mkdir(parents=True, exist_ok=False)
(receipt / 'source.lean.txt').write_bytes(source.read_bytes())
revision = subprocess.check_output(['git','rev-parse','HEAD'], text=True).strip()
host = 'dombarker@100.108.41.90'
workspace = '/home/dombarker/project-offloads/codex-cx-real-r1-20261023'
subprocess.run(['ssh',host,'mkdir -p ' + workspace], check=True)
subprocess.run(['scp',str(source),host + ':' + workspace + '/incoming.lean'], check=True)
subprocess.run(['scp',str(root/'harness/RealR1_run_joint.sh'),host + ':' + workspace + '/run-joint.sh'],check=True)
remote = r'''
import hashlib,json,re,subprocess,time
from pathlib import Path
W=Path(WORKSPACE); J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
p=J/'sources'/REL;p.parent.mkdir(parents=True,exist_ok=True)
if p.exists():
    snap=W/'snapshots'/ATTEMPT/REL;snap.parent.mkdir(parents=True,exist_ok=True)
    snap.write_bytes(p.read_bytes())
    obj=J/'objects'/Path(REL).with_suffix('.olean')
    if obj.exists():snap.with_suffix('.olean').write_bytes(obj.read_bytes())
p.write_bytes((W/'incoming.lean').read_bytes())
seen=set();deps=[]
def imports(text):
    # Remove nested Lean block comments before reading actual import commands.
    clean=[];depth=0;i=0
    while i<len(text):
        if text[i:i+2]=='/-':depth+=1;i+=2
        elif depth and text[i:i+2]=='-/':depth-=1;i+=2
        elif depth:i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i);i=len(text) if j<0 else j
        else:clean.append(text[i]);i+=1
    return re.findall(r'^import (\S+)', ''.join(clean), re.M)

def visit(module):
    if module in seen:return
    seen.add(module)
    r=Path(module.replace('.','/')+'.olean')
    obj=next((d/r for d in paths if (d/r).exists()),None)
    assert obj,('missing cached dependency',module)
    src=J/'sources'/r.with_suffix('.lean')
    deps.append(dict(module=module,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest(),
                     source_sha256=hashlib.sha256(src.read_bytes()).hexdigest() if src.exists() else None))
    if src.exists():
        for m in imports(src.read_text()):visit(m)
for m in imports(p.read_text()):visit(m)
deps.sort(key=lambda x:x['module'])
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
def reservations():
    caps=[]
    for c in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=c.read_text().strip()
            if v!='max' and (c.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(c.parent),bytes=int(v)))
        except OSError:pass
    return caps
start=time.monotonic()
caps=reservations()
while sum(c['bytes'] for c in caps)+8*2**30>55*2**30:
    assert time.monotonic()-start<1800,('reservation hold',caps)
    print('Waiting for host reservation; compiler not launched.',flush=True)
    time.sleep(30)
    caps=reservations()
record=dict(module=REL,attempt=int(ATTEMPT),source_revision=REVISION,
            source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),deps=deps,deps_fingerprint=fp,
            reservations=caps,limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),
            command=['sh',str(W/'run-joint.sh'),ATTEMPT,REL[:-5],'J','7000','8',fp])
(W/('receipt-'+ATTEMPT+'.json')).write_text(json.dumps(record,indent=2)+'\n')
subprocess.run(record['command'],check=True)
'''
for key, val in [('WORKSPACE', workspace), ('REL', rel), ('ATTEMPT',attempt), ('REVISION',revision)]:
    remote = remote.replace(key, repr(val))
result = subprocess.run(['ssh',host,'python3 -'],input=remote,text=True)
for name in ['out-'+attempt+'.log','time-'+attempt+'.log','sha-'+attempt+'.txt']:
    subprocess.run(['scp',host+':/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/'+name,str(receipt/name)],check=True)
subprocess.run(['scp',host+':'+workspace+'/receipt-'+attempt+'.json',str(receipt/'receipt.json')],check=True)
log=(receipt/('out-'+attempt+'.log')).read_text()
record=json.loads((receipt/'receipt.json').read_text())
record.update(exit_status=int(log.split('exit=')[-1].splitlines()[0]),
              axioms=[line for line in log.splitlines() if 'depends on axioms' in line],
              time_log=(receipt/('time-'+attempt+'.log')).read_text())
(receipt/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
sys.exit(record['exit_status'] or result.returncode)
