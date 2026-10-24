#!/usr/bin/env python3
"""Source-only normal-return control proof, diagnostics and negative control."""
from pathlib import Path
import hashlib,json,shutil,tarfile,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'s1-native-word-control-source-only-v1';O.mkdir(exist_ok=False)
def copy(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in range(7):
 name=f's1-original-word-partition-point{p}-bounded-v1';rows.append(name)
rows+=['s1-original-word-exact-v1','s1-original-word-exact-accepted-v1','s1-original-word-partition-point0-v1','s1-word-last-value-negative-v1']
for name in rows:
 root=H/'receipts'/name;assert (root/'receipt.json').is_file(),('not terminal',name)
 for p in root.iterdir():
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,O/'attempts'/name/p.name)
 for suffix in ['input','admission','global-admission','all-local-before','all-local-after','dependency-postcheck']:
  p=H/(name+'-'+suffix+'.json')
  if p.is_file():copy(p,O/'attempts'/name/(suffix+'.json'))
for name in ['s1-claim-word-checks-v1-20261024','s1-claim-word-checks-accepted-v1-20261024','s1-claim-word-partition-v1-20261024','s1-claim-word-negative-v1-20261024']:
 root=H/name
 for p in root.rglob('*'):
  if p.is_file() and not any(x in ['target','.git'] for x in p.relative_to(root).parts) and p.suffix in ['.rs','.toml','.lock','.json','.c','.h']:
   copy(p,O/'inputs'/name/p.relative_to(root))
for name in ['s1-control-loop-inventory-20261024','s1-control-symex-diagnostic-20261024']:
 root=H/name
 for p in root.rglob('*'):
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,O/'diagnostics'/name/p.relative_to(root))
for name in ['prepare-host.py','run-host.py','prepare-accepted-host.py','prepare-partition-host.py','run-partition-host.py','run-remaining-host.py','prepare-negative-host.py','show-control-loops-20261024.py','symex-control-diagnostic-20261024.py']:
 copy(H/name,O/'runners'/name)
copy(H/'s1-word-partition-remaining-v1.json',O/'sequential-plan.json')
# Validate the exact loop IDs used by the successful completeness bounds.
# The binary remains on the host. Hash only; never distribute it.
tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument');pins=[]
for point in range(7):
 files=list((H/'target/kani/x86_64-unknown-linux-gnu/debug/deps').glob(f'*original_and_owned_first_error_point_{point}.out'));assert len(files)==1
 binary=files[0];name=f's1-original-word-partition-point{point}-bounded-v1';inp=json.loads((H/(name+'-input.json')).read_text());cmd=inp['command'];bounds=cmd[cmd.index('--unwindset')+1].split(',')
 # The read-only 2.2MB program loop inventory is a focused metadata query.
 out=subprocess.check_output([str(tool),'--show-loops',str(binary)],text=True)
 ids=[bound.rsplit(':',1)[0] for bound in bounds]
 assert all('Loop '+i+':' in out for i in ids),(point,ids)
 assert all(int(x.rsplit(':',1)[1])==min(point+2,7) for x in bounds)
 (O/f'loop-inventory-point{point}.log').write_text(out)
 pins.append(dict(point=point,path=str(binary),sha256=sha(binary),unwind_bounds=bounds,loop_ids_present=True))
(O/'binary-hash-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',tool_sha256=sha(tool),artifacts=pins,qualification='Hash-only retained GOTO artifacts; source-only packet. Completeness checked by explicit CBMC unwinding assertions.'),indent=2)+'\n')
files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file()}
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,qualification='Seven finite first-error cases cover all normal-return child outcomes, with complete word arguments and numeric call order. Shared leaf contracts are explicit. Not actual arithmetic/abort/SDK or whole S1 closure. No binaries or LLBC distributed.'),indent=2)+'\n')
with tarfile.open(str(O)+'.tar.gz','w:gz') as t:
 for p in O.rglob('*'):
  if p.is_file():t.add(p,arcname=p.relative_to(O))
print(json.dumps(dict(files=len(files),archive=str(O)+'.tar.gz')))
