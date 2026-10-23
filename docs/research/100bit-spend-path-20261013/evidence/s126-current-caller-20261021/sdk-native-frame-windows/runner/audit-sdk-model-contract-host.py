#!/usr/bin/env python3
"""Inspect a checked unary model contract; no equivalence is inferred."""
from pathlib import Path
import json,hashlib,subprocess,shutil,sys,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');mode=sys.argv[1];version=sys.argv[2] if len(sys.argv)>2 else 'v1'
crate=H/f'sdk-live-model-contract-{mode}-{version}';tag=f'sdk-live-model-contract-{mode}-properties-{version}';proof=f'sdk-live-model-contract-{mode}-join-{version}'
target='sdk_live_models::'+('Models::' if version=='v2' else '')+mode
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cut=json.loads((crate/'source-cut.json').read_text());inp=json.loads((H/(proof+'-input.json')).read_text())
assert inp['source_sha256']==sha(crate/'src/lib.rs')==cut['source_sha256']
assert inp['crate_source_pins']['src/sdk_live_models.rs']==sha(crate/'src/sdk_live_models.rs')==cut['model_sha256']
norm=lambda s:re.sub(r'\s+','',s)
assert norm(cut['model_contract_annotation'])==norm(cut['actual_contract_annotation'].replace('self.data','account.data'))
rp=H/'receipts'/proof/'receipt.json';assert json.loads(rp.read_text())['exit_status']==0
snapshot=crate/'checked-metadata';snapshot.mkdir(exist_ok=True)
if not (snapshot/'harness-metadata.json').exists():
 found=[]
 for p in (H/'target/kani').rglob('aspis_s126_sdk_live_model_contract*.kani-metadata.json'):
  for row in json.loads(p.read_text()).get('proof_harnesses',[]):
   if row['pretty_name']=='proofs::actual_sdk_live_contract' and row['attributes']['kind']=={'ProofForContract':{'target_fn':target}}:found.append((p,row))
 assert len(found)==1,found
 p,row=found[0];shutil.copyfile(p,snapshot/'harness-metadata.json');shutil.copyfile(Path(str(row['goto_file']).replace('.symtab.out','.out')),snapshot/'checked.out')
rows=[r for r in json.loads((snapshot/'harness-metadata.json').read_text())['proof_harnesses'] if r['pretty_name']=='proofs::actual_sdk_live_contract'];assert len(rows)==1
row=rows[0];assert row['attributes']['kind']=={'ProofForContract':{'target_fn':target}}
assert not row['attributes']['stubs'] and not row['attributes']['verified_stubs']
program=snapshot/'checked.out';tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',proof_receipt_sha256=sha(rp),proof_input_sha256=sha(H/(proof+'-input.json')),program_sha256=sha(program),harness_metadata_sha256=sha(snapshot/'harness-metadata.json'),harness_metadata=row,source_sha256=sha(crate/'src/lib.rs'),model_sha256=sha(crate/'src/sdk_live_models.rs'),tool_sha256=sha(tool),runner_sha256=sha(Path(__file__)),qualification=__doc__),indent=2)+'\n')
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Inspect checked unary SDK reference contract; no solver replay','--',str(tool),'--show-properties','--json-ui',str(program)])
assert status==0
props=[p for item in json.loads((H/'receipts'/tag/'stdout.log').read_text()) for p in item.get('properties',[])]
selected=[p for p in props if p.get('class') in ['assigns','postcondition','precondition'] or any(w in str(p) for w in ['ensures','old('])]
assert any(p.get('class')=='assigns' for p in selected)
(H/'receipts'/tag/'property-audit.json').write_text(json.dumps(dict(mode=mode,proof_receipt_sha256=sha(rp),program_sha256=sha(program),total_properties=len(props),contract_properties=selected,qualification=__doc__),indent=2)+'\n')
print(json.dumps(dict(mode=mode,properties=len(props),contract_properties=len(selected))))
