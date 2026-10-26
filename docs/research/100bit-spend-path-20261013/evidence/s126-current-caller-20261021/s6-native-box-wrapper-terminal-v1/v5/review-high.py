#!/usr/bin/env python3
"""Review one live owned preprocessing scope; hard cap/reservation unchanged."""
from pathlib import Path
import hashlib,json,subprocess,time
UNIT='aspis-s126-native-box-positive-20261026-v5.scope'
O=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021/native-box-wrapper-20261026-v5')
assert not (O/'resource-review.json').exists()
state=subprocess.run(['systemctl','--user','is-active',UNIT],capture_output=True,text=True)
if state.stdout.strip()!='active':
 (O/'resource-review.json').write_text(json.dumps({'status':'terminal_before_adjustment','changed':False,'time':time.time()})+'\n');raise SystemExit(0)
cg=subprocess.check_output(['systemctl','--user','show',UNIT,'--property=ControlGroup','--value'],text=True).strip()
C=Path('/sys/fs/cgroup')/cg.lstrip('/')
def snapshot():
 return {k:(C/k).read_text().strip() for k in ['memory.max','memory.high','memory.swap.max','memory.current','memory.peak','memory.events']}
before=snapshot();assert before['memory.max']==str(2*2**30) and before['memory.swap.max']=='0'
assert before['memory.high']==str(1536*2**20)
processes={}
for pid in (C/'cgroup.procs').read_text().split():
 try:processes[pid]=(Path('/proc')/pid/'cmdline').read_bytes().decode().split(chr(0))
 except FileNotFoundError:pass
assert any('goto-instrument' in Path(args[0]).name and '--ensure-one-backedge-per-target' in args for args in processes.values())
command=['systemctl','--user','set-property','--runtime',UNIT,'MemoryHigh=1792M']
q=subprocess.run(command,capture_output=True,text=True)
after=snapshot();assert q.returncode==0 and after['memory.high']==str(1792*2**20)
assert after['memory.max']==before['memory.max'] and after['memory.swap.max']=='0'
(O/'resource-review.json').write_text(json.dumps({'status':'reviewed_soft_threshold_adjustment','time':time.time(),'command':command,'exit_status':q.returncode,'before':before,'after':after,'processes':processes,'hard_cap_and_host_reservation_changed':False,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'reason':'Exact instrument pass on3MB focused model exceeds soft threshold; successful focused compiler predecessor and source reduction already retained. No OOM or swap. Raise soft threshold only, within existing2GiB hard cap; mathematical input/source/tool unchanged.'},indent=2)+'\n')
print('MemoryHigh1792MiB; MemoryMax2GiB and swap0 unchanged')
