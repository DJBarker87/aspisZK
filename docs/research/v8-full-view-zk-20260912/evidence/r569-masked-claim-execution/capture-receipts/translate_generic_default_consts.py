#!/usr/bin/env python3
"""Translate the reviewed R569 LLBC with the established pinned Aeneas binary."""
import hashlib,json,pathlib,shlex,subprocess
HERE=pathlib.Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
SSH=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
SCP=['scp','-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
LLBC=HERE/'R569MaskedClaimGenericDefaultConsts.llbc'
LLBC_SHA='707fa2476a0088de8b55069d40ae239372ddcbe5570c26def1f53e7be9391b4d'
assert hashlib.sha256(LLBC.read_bytes()).hexdigest()==LLBC_SHA
remote=r'''import hashlib,json,pathlib,subprocess,sys,os
binary=pathlib.Path(@BIN@); root=pathlib.Path(@OUT@); inp=root/'R569MaskedClaimGenericDefaultConsts.llbc'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(binary)==@BIN_SHA@ and sha(inp)==@LLBC_SHA@
assert not (root/'generated').exists()
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
resources={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert resources=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'},resources
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True)
reservations=[]
for line in units.splitlines():
 p=line.split()
 if p and p[0].startswith('aspis'):
  v=subprocess.check_output(['systemctl','--user','show',p[0],'-p','MemoryMax'],text=True).strip().split('=',1)[1]
  if v.isdigit():reservations.append((p[0],int(v)))
assert sum(v for _,v in reservations)<=40*1024**3,reservations
cmd=[str(binary),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR569MaskedClaimGenericDefaultConsts','-dest',str(root/'generated'),'-subdir','AspisR569MaskedClaimGenericDefaultConsts','-split-files','-emit-json',str(inp)]
(root/'resources.json').write_text(json.dumps({'cgroup':str(cg),'limits':resources,'other_active_aspis_reservations':reservations,'aggregate_limit_bytes':40*1024**3},indent=2)+'\n')
(root/'command.json').write_text(json.dumps({'command':cmd,'llbc_sha256':@LLBC_SHA@,'llbc_bytes':inp.stat().st_size,'aeneas_binary':str(binary),'aeneas_sha256':@BIN_SHA@,'isolated_output':str(root),'scope':'translation only; no Lean compile'},indent=2)+'\n')
with (root/'translation.log').open('w') as log:
 r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=log,stderr=subprocess.STDOUT)
files={str(p.relative_to(root)):sha(p) for p in sorted((root/'generated').rglob('*')) if p.is_file()} if (root/'generated').exists() else {}
result={'exit_status':r.returncode,'llbc_sha256':@LLBC_SHA@,'aeneas_sha256':@BIN_SHA@,'generated_files':files,'lean_compiled':False,'formal_axioms':'N/A; translation only'}
(root/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True); sys.exit(r.returncode)
'''
BIN='/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1'
OUT='/home/dombarker/project-offloads/aspis-r569-masked-claim-generic-default-translate-20261004-a'
BIN_SHA='e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813'
def lit(x):return repr(x)
# Delimited placeholders prevent overlapping key substitution.
assert '@BIN@' in remote and '@OUT@' in remote and '@BIN_SHA@' in remote and '@LLBC_SHA@' in remote
for k,v in {'BIN':BIN,'OUT':OUT,'BIN_SHA':BIN_SHA,'LLBC_SHA':LLBC_SHA}.items():remote=remote.replace('@'+k+'@',lit(v))
unit='aspis-r569-generic-default-translate-20261004'
launch=['systemd-run','--user','--wait','--collect','--pipe',f'--unit={unit}','--working-directory=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830','-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','python3','-c',remote]
(HERE/'R569-generic-default-translation-launch.json').write_text(json.dumps({'unit':unit,'systemd_argv':launch,'caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},'aeneas_sha256':BIN_SHA,'llbc_sha256':LLBC_SHA,'output':OUT},indent=2)+'\n')
# Fresh isolated remote output; input is the already-verified local LLBC bytes.
subprocess.run([*SSH,HOST,'mkdir','-m','700',OUT],check=True)
subprocess.run([*SCP,str(LLBC),f'{HOST}:{OUT}/R569MaskedClaimGenericDefaultConsts.llbc'],check=True)
with (HERE/'R569-generic-default-translation-ssh-output.log').open('w') as out:r=subprocess.run([*SSH,HOST,shlex.join(launch)],stdout=out,stderr=subprocess.STDOUT)
(HERE/'R569-generic-default-translation-launch-exit.txt').write_text(str(r.returncode)+'\n')
# Fetch files after generated; transfer whole focused evidence directory.
for rel in ['resources.json','command.json','translation.log','result.json']:
 subprocess.run([*SCP,f'{HOST}:{OUT}/{rel}',str(HERE/('generic-default-translated-'+rel))],check=True)
if r.returncode:raise SystemExit(r.returncode)
subprocess.run([*SSH,HOST,'tar','-C',OUT,'-czf',f'{OUT}/generated.tgz','generated'],check=True)
subprocess.run([*SCP,f'{HOST}:{OUT}/generated.tgz',str(HERE/'R569-generic-default-generated.tgz')],check=True)
