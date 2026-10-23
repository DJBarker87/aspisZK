#!/usr/bin/env python3
"""Named finite proof-window gates, fresh admission/caps for each operation.
Expected time is in each CBMC all-properties window (~140s in predecessor),
not compilation (~2s), generation or a dense arithmetic computation. Each
worker is sequential. The queue stops at the first unproved or unaudited case.
It launches ordinary processes, not agents; every compiler/solver has its own
6G/8G/Swap0 scope from the pinned runners. Audit scopes use1G/2G/Swap0.
"""
from pathlib import Path
import subprocess,json,hashlib,sys,time
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
worker=sys.argv[1];windows=list(map(int,sys.argv[2:]));assert worker in ['a','b']
assert len(windows)==len(set(windows)) and all(1<=w<15 for w in windows)
O=H/f'sdk-native-window-queue-{worker}-v1';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(O/'input.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',worker=worker,windows=windows,runner_sha256=sha(Path(__file__)),source_pins={str(w):sha(H/f'sdk-shared-prefix-window{w}-v1/src/lib.rs') for w in windows},kit_pins={n:sha(H/'kit'/n) for n in ['run-modular-host.py','run-sdk-shared-prefix-host.py','audit-native-root-frame-host.py','reservation.py','capped.py']},qualification=__doc__),indent=2)+'\n')
for w in windows:
 version=f'window{w}-v1';proof=f'sdk-native-proof-window{w}-all-v1'
 operations=[('codegen',['python3',str(H/'kit/run-modular-host.py'),f'sdk-shared-prefix-codegen-{version}',str(H/f'sdk-shared-prefix-{version}'),'proofs::native_owned_decoder_prefix','codegen-stubbing'],0),('proof',['python3',str(H/'kit/run-sdk-shared-prefix-host.py'),proof,version,'pointwise','plain'],10),('audit',['python3',str(H/'kit/audit-native-root-frame-host.py'),'0',proof],0)]
 for stage,cmd,expected in operations:
  event=O/f'window{w}-{stage}.json';assert not event.exists()
  (O/'active.json').write_text(json.dumps(dict(window=w,stage=stage,command=cmd,started_utc=time.time()),indent=2)+'\n')
  start=time.monotonic()
  with (O/f'window{w}-{stage}.log').open('w') as log:result=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
  event.write_text(json.dumps(dict(window=w,stage=stage,command=cmd,exit_status=result.returncode,expected_exit_status=expected,wall_seconds=time.monotonic()-start,qualification='Queue status only; gate/audit receipts and complete properties determine evidence.'),indent=2)+'\n')
  print(json.dumps(dict(worker=worker,window=w,stage=stage,exit_status=result.returncode)),flush=True)
  if result.returncode!=expected:raise SystemExit('Stopped at unproved/unaudited case; do not restart unchanged.')
(O/'complete.json').write_text(json.dumps(dict(worker=worker,windows=windows,status='named_cases_checked_and_audited',qualification='Need full index coverage and native/source/caller/scan/runtime composition; not S2 closure.'),indent=2)+'\n')
