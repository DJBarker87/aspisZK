#!/usr/bin/env python3
"""Change only this job's two proof inputs, preserving its native build cache."""
from pathlib import Path
import base64,hashlib,json,subprocess,time
W=Path(__file__).resolve().parent
B=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021/native-box-wrapper-20261026-v1')
d=json.loads((W/'source-update.json').read_text())
assert set(d['changes'])=={'binding.json','harness/src/lib.rs'}
assert not (W/'source-update-receipt.json').exists()
units={}
for v in ['v1','v3','v4','v5']:
 unit='aspis-s126-native-box-positive-20261026-'+v+'.scope'
 q=subprocess.run(['systemctl','--user','is-active',unit],capture_output=True,text=True)
 assert q.stdout.strip()=='inactive',(unit,q.stdout,q.stderr)
 units[unit]=q.stdout.strip()
def pins():
 return {p:hashlib.sha256((B/p).read_bytes()).hexdigest() for p in d['before']}
assert pins()==d['before']
for p,encoded in d['changes'].items():
 target=B/p;temp=target.with_name(target.name+'.s126-update-temp')
 assert not temp.exists()
 temp.write_bytes(base64.b64decode(encoded,validate=True));temp.replace(target)
assert pins()==d['after']
(W/'source-update-receipt.json').write_text(json.dumps({'exit_status':0,'time':time.time(),'before_pins_verified':True,'after_pins_verified':True,'changed':list(d['changes']),'prior_scopes':units,'native_crates_changed':False,'build_cache_preserved':True,'update_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},indent=2)+'\n')
print('owned proof-only source update: PASS; native dependencies and build cache retained')
