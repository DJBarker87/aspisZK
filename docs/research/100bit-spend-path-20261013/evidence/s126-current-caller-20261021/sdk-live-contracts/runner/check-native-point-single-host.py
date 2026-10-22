#!/usr/bin/env python3
"""First partition: the named byte-frame property on original SDK source.
All other properties remain unproved at this partition. A whole certificate
requires their complete checked union, including safety/unwinding and covers.
"""
from pathlib import Path
import json,subprocess,sys,hashlib,signal,os,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');tag='sdk-native-point-single-v1';O=H/tag
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if 'run' not in sys.argv:
 O.mkdir(exist_ok=False)
 inventory=H/'receipts/sdk-native-point-frame-properties-v1/stdout.log'
 props=[p for item in json.loads(inventory.read_text()) for p in item.get('properties',[])]
 selected=[p for p in props if p['description']=='"arbitrary native-prefix account byte preserved"'];assert len(selected)==1
 old=H/'sdk-native-point-frame-plain-v1-input.json';data=json.loads(old.read_text());cmd=data['command'].copy()
 assert '--property' not in cmd and '--json-ui' not in cmd
 cmd[-1:-1]=['--property',selected[0]['name']]
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,predecessor_input_sha256=sha(old),property_inventory_sha256=sha(inventory),selected_properties=selected,unselected_property_count=len(props)-len(selected),program_sha256=sha(Path(cmd[-1])),tool_sha256=sha(Path(cmd[0])),runner_sha256=sha(Path(__file__)),qualification=__doc__,timeout_seconds=180),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Named original-SDK byte-frame partition; other safety/properties require a checked complete union; no full frame/whole caller claim','--','python3',__file__,'run']))
cmd=json.loads((H/(tag+'-input.json')).read_text())['command']
with (O/'cbmc.log').open('w') as log:
 p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 try:p.wait(timeout=180)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGKILL);p.wait();(O/'timeout.json').write_text(json.dumps(dict(status='not_proved',reason='180s deadline'))+'\n');raise
rows=[]
for line in (O/'cbmc.log').read_text().splitlines():
 m=re.fullmatch(r'\[([^\]]+)\] (.*): (SUCCESS|FAILURE|UNKNOWN|NOT_CHECKED|UNREACHABLE)',line)
 if m:rows.append(dict(property=m[1],description=m[2],status=m[3]))
(O/'properties-without-traces.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'cbmc-exit.json').write_text(json.dumps(dict(exit_status=p.returncode,qualification=__doc__),indent=2)+'\n')
raise SystemExit(p.returncode)
