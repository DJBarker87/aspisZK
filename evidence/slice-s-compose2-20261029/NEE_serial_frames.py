"""Serial independent native frame attempts; never repeat a failed shape."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
sequence=[('parts','negative')]+[(c,k) for c in ['transfer_common','withdrawal_common','canonical','validate_common','validate_transfer','validate_withdrawal'] for k in ['positive','negative']]
for n,(case,control) in enumerate(sequence,10):
    a=f'NEE_K{n:03}'
    if (E/a/'receipt.json').exists():raise SystemExit('Never resume or repeat this sequence unchanged')
    r=subprocess.run([sys.executable,str(E/'NEE_prepare_frame.py'),case,control],capture_output=True,text=True)
    if r.returncode:raise SystemExit(r.stdout+r.stderr)
    h=r.stdout.strip()
    r=subprocess.run([sys.executable,str(E/'NEE_kani_run.py'),a,'kani',h])
    receipt=E/a/'receipt.json'
    if not receipt.exists():raise SystemExit('Missing receipt; recover read-only, never relaunch')
    rc=json.loads(receipt.read_text())
    with (E/'NEE_FRAME_SEQUENCE.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,case=case,control=control,exit=rc['exit_status']))+'\n')
    log=(E/a/'stdout.log').read_text()
    if control=='positive' and rc['exit_status']!=0:
        print('OPEN native frame:',case,flush=True)
    elif control=='negative' and ('Failed Checks:' not in log or 'CBMC timed out' in log):
        print('OPEN matched control:',case,flush=True)
