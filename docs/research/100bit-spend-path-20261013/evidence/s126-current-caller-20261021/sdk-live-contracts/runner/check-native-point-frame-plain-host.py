#!/usr/bin/env python3
"""Check identical compiled properties with plain output, avoiding JSON traces.

CBMC enables error traces implicitly for JSON UI. The predecessor log reached
SAT and trace construction before timeout. Only output format changes here;
all properties, source, binary, solver, unwind and resource limits are pinned.
No result is inferred until the complete property report is available.
"""
from pathlib import Path
import hashlib,json,subprocess,sys,os,signal,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
tag='sdk-native-point-frame-plain-v1';old='sdk-native-point-frame-check-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
O=H/tag
if 'run' not in sys.argv:
 O.mkdir(exist_ok=False)
 inp=json.loads((H/(old+'-input.json')).read_text())
 cmd=inp['commands'][-1].copy();assert cmd.count('--json-ui')==1;cmd.remove('--json-ui')
 assert Path(cmd[-1]).is_file()
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',predecessor_input_sha256=sha(H/(old+'-input.json')),predecessor_receipt_sha256=sha(H/'receipts'/old/'receipt.json'),program_sha256=sha(Path(cmd[-1])),cbmc_sha256=sha(Path(cmd[0])),runner_sha256=sha(Path(__file__)),command=cmd,qualification=__doc__,timeout_seconds=180),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Identical native point-frame target, plain property output avoids implicit JSON counterexample traces; all assertions remain enabled','--','python3',__file__,'run']))
cmd=json.loads((H/(tag+'-input.json')).read_text())['command']
with (O/'cbmc.log').open('w') as log:
 p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 try:p.wait(timeout=180)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGKILL);p.wait()
  (O/'timeout.json').write_text(json.dumps(dict(status='not_proved',reason='180s deadline; same cap'))+'\n');raise
s=(O/'cbmc.log').read_text()
properties=[]
for line in s.splitlines():
 m=re.fullmatch(r'\[([^\]]+)\] (.*): (SUCCESS|FAILURE|UNKNOWN|NOT_CHECKED|UNREACHABLE)',line)
 if m:properties.append(dict(property=m[1],description=m[2],status=m[3]))
(O/'properties-without-traces.json').write_text(json.dumps(properties,indent=2)+'\n')
(O/'cbmc-exit.json').write_text(json.dumps(dict(exit_status=p.returncode,property_rows=len(properties),qualification='Plain report; actual property IDs/descriptions distinguish expected reached covers from failures. No success is inferred from exit10 alone.'),indent=2)+'\n')
raise SystemExit(p.returncode)
