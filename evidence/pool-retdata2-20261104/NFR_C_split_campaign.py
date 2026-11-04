"""Lane-owned serial independent observation packets; receipts are authoritative."""
from pathlib import Path
import json,subprocess,sys,shutil
E=Path(__file__).resolve().parent
modes=['byte','byte-negative']+[f'value-{f}{n}' for f in range(8) for n in ['', '-negative']]
ids=list(range(13,30))+[61]
for i,mode in zip(ids,modes):
 a=f'NFR_K{i:03}'
 if (E/a/'receipt.json').exists():continue
 subprocess.run([sys.executable,str(E/'NFR_C_split.py'),mode],check=True)
 shutil.copyfile(E/'NFR_C_native.patch',E/'NFR_native.patch');shutil.copyfile(E/'NFR_C_CURRENT.json',E/'NFR_CURRENT.json')
 r=subprocess.run([sys.executable,str(E/'NFR_kani_run.py'),a,'pair_forest_dispatch::NFR_CJoin::association'],capture_output=True,text=True)
 (E/(a+'-split.log')).write_text(r.stdout+r.stderr)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP missing receipt '+a)
 rc=json.loads((E/a/'receipt.json').read_text());s=(E/a/'stdout.log').read_text()
 timeout='timed out' in s.lower();unwind='Failed Checks: unwinding' in s
 with (E/'NFR_C_SPLIT_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,mode=mode,exit=rc['exit_status'],timeout=timeout,unwind=unwind))+'\n')
 print(a,mode,rc['exit_status'],'timeout' if timeout else 'unwind' if unwind else '',flush=True)
 if timeout or unwind or rc['exit_status']!=(1 if mode.endswith('negative') else 0):raise SystemExit('REVIEW split before next launch')
