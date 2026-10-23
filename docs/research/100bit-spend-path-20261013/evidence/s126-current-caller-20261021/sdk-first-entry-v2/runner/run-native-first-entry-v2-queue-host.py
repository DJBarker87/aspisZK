#!/usr/bin/env python3
"""Sequential finite entry-coordinate cases; capped runners perform fresh admission.
Expected time in named CBMC entry check, compilation about2s. Stop on any failure.
"""
from pathlib import Path
import subprocess,sys,json,time,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');worker=sys.argv[1];versions=sys.argv[2:];assert worker in ['a','b']
O=H/f'sdk-first-entry-queue-{worker}-v2';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(O/'input.json').write_text(json.dumps(dict(versions=versions,runner_sha256=sha(Path(__file__)),kit_pins={n:sha(H/'kit'/n) for n in ['run-modular-host.py','run-sdk-shared-prefix-host.py','audit-native-first-entry-host.py','reservation.py','capped.py']},qualification=__doc__),indent=2)+'\n')
for v in versions:
 tag='sdk-'+v
 ops=[('codegen',['python3',str(H/'kit/run-modular-host.py'),'sdk-shared-prefix-codegen-'+v,str(H/('sdk-shared-prefix-'+v)),'proofs::native_owned_decoder_prefix','codegen-stubbing','short'],0),('proof',['python3',str(H/'kit/run-sdk-shared-prefix-host.py'),tag,v,'first-coupling','coupled-cmp','pointwise','native-first-frame','native-first-entry','plain'],10),('audit',['python3',str(H/'kit/audit-native-first-entry-host.py'),tag],0)]
 for stage,cmd,expected in ops:
  start=time.monotonic();(O/'active.json').write_text(json.dumps(dict(version=v,stage=stage,command=cmd))+'\n')
  with (O/(v+'-'+stage+'.log')).open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
  event=dict(version=v,stage=stage,exit_status=r.returncode,expected=expected,wall_seconds=time.monotonic()-start)
  (O/(v+'-'+stage+'.json')).write_text(json.dumps(event,indent=2)+'\n');print(json.dumps(event),flush=True)
  if r.returncode!=expected:raise SystemExit('Unproved/unaudited case; stopped. No unchanged retry.')
(O/'complete.json').write_text(json.dumps(dict(versions=versions,status='all_named_cases_audited',qualification='Coordinate entry gates only; source/caller/runtime/children/continuation composition remains.'))+'\n')
