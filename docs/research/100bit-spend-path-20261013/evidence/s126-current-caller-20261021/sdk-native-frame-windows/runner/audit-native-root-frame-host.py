#!/usr/bin/env python3
"""Audit an actual SDK root case against the exact enabled property inventory.
No solver replay. Plain all-properties output must cover the complete inventory;
only source-classified covers may fail (their failure means reached).
"""
from pathlib import Path
import json,hashlib,subprocess,sys,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');root=int(sys.argv[1]);assert 0<=root<3
proof=sys.argv[2] if len(sys.argv)>2 else f'sdk-native-root{root}-all-v1'
tag=proof+'-audit' if len(sys.argv)>2 else f'sdk-native-root{root}-audit-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inpfile=H/(proof+'-input.json');inp=json.loads(inpfile.read_text());cmd=inp['commands'][-1].copy()
assert '--property' not in cmd and '--json-ui' not in cmd
assert inp['harness_metadata']['attributes']['stubs'] and not any('sdk_live_models' in str(p) for p in inp['harness_metadata']['attributes']['stubs'])
rp=H/'receipts'/proof/'receipt.json';receipt=json.loads(rp.read_text());assert receipt['exit_status']==10 and receipt['swaps']==0
program=Path(cmd[-1]);assert program.is_file()
cmd[-1:-1]=['--show-properties','--json-ui']
if not (H/'receipts'/tag/'receipt.json').exists():
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,proof_input_sha256=sha(inpfile),proof_receipt_sha256=sha(rp),program_sha256=sha(program),tool_sha256=sha(Path(cmd[0])),runner_sha256=sha(Path(__file__)),qualification=__doc__),indent=2)+'\n')
 status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Inventory exact enabled native root properties, no solver replay','--',*cmd]);assert status==0
else:
 old=json.loads((H/(tag+'-input.json')).read_text())
 assert old['program_sha256']==sha(program) and old['command']==cmd
 assert json.loads((H/'receipts'/tag/'receipt.json').read_text())['exit_status']==0
props=[p for item in json.loads((H/'receipts'/tag/'stdout.log').read_text()) for p in item.get('properties',[])]
raw=H/proof/'step7.log';assert raw.is_file()
expected={p['name']:p for p in props}
# The first renderer used [^]] for IDs and lost IDs containing Rust slice/array
# types. Keep it as historical evidence; reconstruct from the complete raw log
# using exact inventory IDs, never guessing which closing bracket ends an ID.
rows=[];current=None;block=[]
for line in raw.read_text().splitlines():
 end=line.find('] ') if line.startswith('[') else -1
 while end>=0 and line[1:end] not in expected:end=line.find('] ',end+2)
 if end>=0:
  assert current is None,('unterminated property',current)
  current=line[1:end];block=[line[end+2:]]
 elif current is not None:block.append(line)
 if current is not None:
  match=re.fullmatch(r'(.*): (SUCCESS|FAILURE|UNKNOWN|UNREACHABLE|NOT CHECKED|ERROR)','\n'.join(block),re.S)
  if match:
   rows.append(dict(property=current,description=match[1],status=match[2]));current=None;block=[]
assert current is None,('unterminated final property',current)
(H/'receipts'/tag/'properties-complete-v2.json').write_text(json.dumps(rows,indent=2)+'\n')
expected={p['name']:p for p in props};actual={r['property']:r for r in rows}
assert len(expected)==len(props) and len(actual)==len(rows)
assert expected.keys()==actual.keys(),dict(expected=len(expected),actual=len(actual),missing=list(expected.keys()-actual.keys())[:10],extra=list(actual.keys()-expected.keys())[:10])
covers=[p['name'] for p in props if p['class']=='cover'];assert len(covers)==2,covers
assert all(r['status']==('FAILURE' if r['property'] in covers else 'SUCCESS') for r in rows)
frame=[p for p in props if p['description']=='"arbitrary native-prefix account byte preserved"'];assert len(frame)==1
assert actual[frame[0]['name']]['status']=='SUCCESS'
(H/'receipts'/tag/'property-audit-v2.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',root=root,proof_receipt_sha256=sha(rp),program_sha256=sha(program),inventory_sha256=sha(H/'receipts'/tag/'stdout.log'),raw_log_sha256=sha(raw),property_report_sha256=sha(H/'receipts'/tag/'properties-complete-v2.json'),auditor_sha256=sha(Path(__file__)),old_incomplete_renderer_sha256=sha(H/proof/'properties-without-traces.json'),inventory_properties=len(props),noncover_successes=len(props)-len(covers),reached_covers=covers,frame_property=frame[0],qualification=__doc__+' Exact ID inventory reconciled with the complete raw log, including Rust IDs with brackets. Decoder-error prefix/pure-scan abstraction and runtime/child/success joins remain explicit. This is a checked whole-property root case, not whole S2.'),indent=2)+'\n')
print(json.dumps(dict(root=root,properties=len(props),noncover_successes=len(props)-len(covers),reached_covers=len(covers))))
