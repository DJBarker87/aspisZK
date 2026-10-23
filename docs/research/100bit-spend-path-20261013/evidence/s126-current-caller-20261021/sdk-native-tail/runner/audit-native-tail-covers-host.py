#!/usr/bin/env python3
"""Inventory and targeted coverage evidence omitted by the prior terse run.
No assertion replay: the original2085-check success receipt is authoritative.
Only this source chunk's three source cover intentions are queried, including duplicated compiler
locations. Each intention must have a reached location; unreachable duplicate
locations are recorded separately, never claimed reached.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');root=int(sys.argv[1]);tag=f'sdk-native-post-first-tail-root{root}-check-v5';P=H/f'sdk-native-post-first-tail-root{root}-v5';proof=H/'receipts'/tag/'receipt.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads(proof.read_text());assert r['exit_status']==0 and r['swaps']==0
matches=[]
for p in (H/'target/kani').rglob(f'aspis_s126_sdk_native_post_first_tail_root{root}_v5*.kani-metadata.json'):
 for row in json.loads(p.read_text()).get('proof_harnesses',[]):
  if row['pretty_name']=='proofs::native_post_first_tail':matches.append((p,row))
assert len(matches)==1;metadata,row=matches[0];raw=Path(row['goto_file']);program=Path(str(raw).replace('.symtab.out','.out'));tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')
assert row['attributes']['kind']=='Proof' and not row['attributes']['stubs'] and row['attributes']['verified_stubs']==['encoded_finish']
O=H/(tag+'-audit-v2');O.mkdir(exist_ok=False)
def run(name,cmd,high,max_,purpose):
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(name+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(name+'-input.json')).write_text(json.dumps(dict(command=cmd,program_sha256=sha(program),source_sha256=sha(P/'src/lib.rs'),proof_receipt_sha256=sha(proof),harness_metadata=row,metadata_sha256=sha(metadata),runner_sha256=sha(Path(__file__)),qualification=purpose),indent=2)+'\n')
 return subprocess.call(['systemd-run','--user','--scope','-q','-p',f'MemoryHigh={high}','-p',f'MemoryMax={max_}','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/name),purpose,'--',*cmd])
inv=tag+'-inventory'
if not (H/'receipts'/inv/'receipt.json').exists():assert run(inv,[str(tool),'--show-properties','--json-ui',str(program)],'1G','2G','Inventory only; no solver')==0
else:assert json.loads((H/(inv+'-input.json')).read_text())['program_sha256']==sha(program)
props=[p for x in json.loads((H/'receipts'/inv/'stdout.log').read_text()) for p in x.get('properties',[])];covers=[p for p in props if p['class']=='cover'];wanted=[p for p in covers if p['description'].startswith('native tail ')];assert len({p['description'] for p in wanted})==3
cmd=[str(tool),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','1772','--sat-solver','cadical','--slice-formula','--unwinding-assertions']
for p in wanted:cmd+=['--property',p['name']]
cmd+=[str(program)];name=tag+'-covers-v2';cmd=['/usr/bin/timeout','180',*cmd];status=run(name,cmd,'3G','4G','Only3 source-tail cover intentions/duplicated locations missing from terse artifact; no assertion replay.');assert status==10
log=(H/'receipts'/name/'stdout.log').read_text()
statuses={p['name']:next(line.rsplit(': ',1)[1] for line in log.splitlines() if line.startswith('['+p['name']+']') and line.endswith((': FAILURE',': SUCCESS'))) for p in wanted}
assert all(any(statuses[p['name']]=='FAILURE' for p in wanted if p['description']==description) for description in {p['description'] for p in wanted})
(O/'audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',root=root,source_sha256=sha(P/'src/lib.rs'),program_sha256=sha(program),proof_receipt_sha256=sha(proof),enabled_properties=len(props),noncovers=len(props)-len(covers),covers=covers,reached_source_covers=[p for p in wanted if statuses[p['name']]=='FAILURE'],unreached_duplicate_locations=[p for p in wanted if statuses[p['name']]=='SUCCESS'],statuses=statuses,qualification=__doc__),indent=2)+'\n')
print(json.dumps(dict(root=root,noncovers=len(props)-len(covers),all_covers=len(covers),reached_source_intentions=3)))
