from pathlib import Path
import json,hashlib
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(B.glob('NKR_K[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];x=json.loads((B/(a+'.json')).read_text());assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert json.loads((B/(a+'-reservation.json')).read_text())['allowed'] is True
 assert x['env']['CARGO_TARGET_DIR']==str(B/'NKR_target') and x['env']['CARGO_NET_OFFLINE']=='true'
 assert x['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 for n,h in r['source_hashes'].items():assert sha(p.parent/'sources'/n)==h,(a,n)
 g=B/(a+'-graph-check.json');lock=B/(a+'-lock-check.json')
 if g.exists():assert json.loads(g.read_text())['graph_matches_frozen']
 if lock.exists():assert json.loads(lock.read_text())['unchanged']
 if 'Checking harness'in(p.parent/'stdout.log').read_text():assert g.exists()and lock.exists(),a
 rows.append(dict(attempt=a,exit_status=r['exit_status'],source_revision=r['source_revision'],receipt_sha256=sha(p)))
assert len(rows)==69,len(rows)
S=B/'NKR_src';pins={**json.loads((B/'NKR_FROZEN_FILE_PINS.json').read_text()),**json.loads((B/'NKR_SOURCE_PINS.json').read_text())}
assert all(sha(S/n)==h for n,h in pins.items())
assert sha(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(B/'NKR_KMX.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
(B/'NKR_NATIVE_RELEASE.json').write_text(json.dumps(dict(status='PASS',prior_native_scopes=len(rows),actual_current_source_files=len(pins),source_lock_unchanged=True,all_receipt_inputs_hash_checked=True,scopes=rows,kmx_patch_sha256=sha(B/'NKR_KMX.patch'),CARGO_TARGET_DIR=str(B/'NKR_target')),indent=1));print('69 native scope receipts, their exact inputs, frozen source/lock/features and KMX pins validated')
