"""Additional edge controls; existing positive receipts are never rerun."""
from pathlib import Path
import json,subprocess,sys,shutil
E=Path(__file__).resolve().parent
modes=['runtime-context','runtime-order','decode-pointer','decode-length','saved-frame','validator-place','lane-place','encoder-place','decoded-output']
for i,mode in enumerate(modes,62):
 a=f'NFR_K{i:03}'
 if (E/a/'receipt.json').exists():continue
 subprocess.run([sys.executable,str(E/'NFR_C_controls.py'),mode],check=True)
 shutil.copyfile(E/'NFR_C_native.patch',E/'NFR_native.patch');shutil.copyfile(E/'NFR_C_CURRENT.json',E/'NFR_CURRENT.json')
 r=subprocess.run([sys.executable,str(E/'NFR_kani_run.py'),a,'pair_forest_dispatch::NFR_CJoin::association'],capture_output=True,text=True)
 (E/(a+'-edge-control.log')).write_text(r.stdout+r.stderr)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP missing receipt '+a)
 rc=json.loads((E/a/'receipt.json').read_text());s=(E/a/'stdout.log').read_text();shape=json.loads((E/(a+'-shape.json')).read_text())
 timeout='timed out' in s.lower();unwind='Failed Checks: unwinding' in s
 match=rc['exit_status']==1 and 'VERIFICATION:- FAILED' in s and not timeout and not unwind and 'Failed Checks: assertion' in s
 with (E/'NFR_C_EDGE_CONTROLS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,mode=mode,exit=rc['exit_status'],timeout=timeout,unwind=unwind,matched=match,positive=shape['matched_positive']))+'\n')
 print(a,mode,rc['exit_status'],'matched' if match else 'REVIEW',flush=True)
 if not match:raise SystemExit('REVIEW unexpected control before next launch')
