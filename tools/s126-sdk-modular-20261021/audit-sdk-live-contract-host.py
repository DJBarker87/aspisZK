#!/usr/bin/env python3
"""Snapshot and inspect a checked actual SDK method contract; no solver replay.
Only source/property metadata and compiled-artifact hashes are exportable.
"""
from pathlib import Path
import json,hashlib,subprocess,sys,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
mode=sys.argv[1];version=sys.argv[2] if len(sys.argv)>2 else 'v1'
assert mode in ['length','shared','exclusive']
sdk=H/('sdk-account-info-'+mode+'-'+version);crate=H/('sdk-live-'+mode+'-'+version)
tag='sdk-live-'+mode+'-properties-'+version;proof='sdk-live-'+mode+'-join-'+version
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cut=json.loads((crate/'source-cut.json').read_text())
assert cut['annotated_sdk_source_sha256']==sha(sdk/'src/lib.rs')
stripped=(sdk/'src/lib.rs').read_text().replace(cut['annotation'],'')
assert hashlib.sha256(stripped.encode()).hexdigest()==cut['original_sdk_source_sha256']
assert sha(crate/'src/lib.rs')==cut['harness_source_sha256']
rp=H/'receipts'/proof/'receipt.json';receipt=json.loads(rp.read_text())
assert receipt['exit_status']==0 and receipt['swaps']==0
pin=H/(proof+'-input.json');data=json.loads(pin.read_text())
assert data['source_sha256']==sha(crate/'src/lib.rs')
selected=[]
for meta in (H/'target/kani').rglob('aspis_s126_sdk_live_borrow_contract*.kani-metadata.json'):
 for row in json.loads(meta.read_text()).get('proof_harnesses',[]):
  if row['pretty_name']=='proofs::actual_sdk_live_contract' and row['attributes']['kind']=={'ProofForContract':{'target_fn':'AccountInfo::'+cut['method']}}:
   selected.append((meta,row))
assert len(selected)==1,selected
meta,row=selected[0]
assert row['attributes']['stubs']==[] and row['attributes']['verified_stubs']==[]
assert 'solana_account_info' in row['contract']['contracted_function_name']
program=Path(str(row['goto_file']).replace('.symtab.out','.out'))
snapshot=H/(tag+'-snapshot');snapshot.mkdir(exist_ok=False)
shutil.copyfile(program,snapshot/'checked.out')
shutil.copyfile(meta,snapshot/'harness-metadata.json')
cbmc=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')
out=H/'receipts'/tag
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',proof_receipt_sha256=sha(rp),proof_input_sha256=sha(pin),harness_source_sha256=sha(crate/'src/lib.rs'),annotated_sdk_source_sha256=sha(sdk/'src/lib.rs'),original_sdk_source_sha256=cut['original_sdk_source_sha256'],program_sha256=sha(snapshot/'checked.out'),harness_metadata_sha256=sha(meta),harness_metadata=row,cbmc_sha256=sha(cbmc),runner_sha256=sha(Path(__file__)),sdk_source_pins={str(p.relative_to(sdk)):sha(p) for p in sdk.rglob('*') if p.is_file()},qualification=__doc__+' This is a checked concrete external SDK method, not a newly implemented wrapper. Method body equivalence is byte-for-byte restoration by removing the recorded proof annotations. The harness covers its explicit finite heap domain, not arbitrary runtime heaps.'),indent=2)+'\n')
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(out),'Read checked actual SDK method contract properties, preserve program hash before next codegen; no solver replay','--',str(cbmc),'--show-properties','--json-ui',str(snapshot/'checked.out')])
assert status==0,status
properties=[p for item in json.loads((out/'stdout.log').read_text()) for p in item.get('properties',[])]
interesting=[p for p in properties if p.get('class') in ['assigns','postcondition','precondition'] or any(w in str(p).lower() for w in ['ensures','old('])]
assert any(p.get('class')=='assigns' and cut['method'] in str(p) for p in interesting)
assert any('old(' in str(p) or 'postcondition' in str(p) or 'ensures' in str(p) for p in interesting)
(out/'property-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',method=cut['method'],program_sha256=sha(snapshot/'checked.out'),proof_receipt_sha256=sha(rp),total_properties=len(properties),contract_properties=interesting,qualification=__doc__+' Actual proof is the pinned successful all-properties Kani receipt; no proof is inferred from metadata alone.'),indent=2)+'\n')
print(json.dumps(dict(method=cut['method'],properties=len(properties),contract_properties=len(interesting))))
