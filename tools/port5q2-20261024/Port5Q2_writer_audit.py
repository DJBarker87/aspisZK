#!/usr/bin/env python3
"""Revalidate the existing production-buffer certificate, never replay it."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port5q2-20261024';old=R/'evidence/ports3-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((old/'kani-001/receipt.json').read_text());assert r['exit_status']==0
assert 'VERIFICATION SUCCESSFUL' in (old/'kani-001/stdout.log').read_text()
pins=r['deps_fingerprint']['source_snapshot_pins'];assert all(sha(R/k)==v for k,v in pins.items())
current=R/'tools/ports3-20261023/writer-reached/src/lib.rs'
src=old/'kani-001/sources/writer-reached/src/lib.rs'
assert current.read_bytes().startswith(src.read_bytes()), 'Changed writer harness dependency prefix'
assert sha(src)==r['source_hashes']['writer-reached/src/lib.rs']
assert 'let proof:[u8;57607]=kani::any();let public:[u8;1880]=kani::any();' in src.read_text()
assert 'fn production_buffers_writer()' in src.read_text()
contract=json.loads((old/'kani-002/receipt.json').read_text());assert contract['exit_status']==0
assert 'VERIFICATION SUCCESSFUL' in (old/'kani-002/stdout.log').read_text()
assert contract['source_hashes']['writer-reached/src/lib.rs']==sha(src)
x={'schema':'port5q2-native-writer-certificate-admission-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'native_certificate':{'path':str((old/'kani-001/receipt.json').relative_to(R)),'sha256':sha(old/'kani-001/receipt.json'),'target':'proofs::production_buffers_writer','exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],'source_revision':r['source_revision'],'print_axioms':r['print_axioms']},'encoder_contract_receipt_sha256':sha(old/'kani-002/receipt.json'),'current_source_snapshot_pins':pins,'harness_sha256':sha(src),'current_harness_relation':'Exact retained writer file is a byte prefix; only independent production_reader module appended later','domain':['S2','weights length64','next10','canonical WideExact fields','arbitrary raw K fields','proof length57607','public length1880'],'conclusion':'Native checkpoint returns1768 bytes; every byte equals sparse body_byte plus checksum; digest input pointer/length identity and order, arbitrary selected checksum-body byte. All1688 checks passed.','admission':'Port5Q2_Prepared.reached proves S2/next10/size64 and stronger canonical raw fields on the SAME installed prefix under named Session A contracts. Caller length1880 and physical/native runtime/P6 carrier instantiation remain explicit; no full frozen2 semantic binding or ELF result inferred.','new_kani_runs':0,'new_rust_runs':0,'no_replay_reason':'Unchanged source and accepted certificate reused per AGENTS.md cadence.'}
(E/'writer-admission.json').write_text(json.dumps(x,indent=2)+'\n');print('PASS:173 current source pins; production writer and encode contract reused')
