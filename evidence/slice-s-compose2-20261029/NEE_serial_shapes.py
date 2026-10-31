"""Consume only the remaining twelve Kani slots on required shape fidelity."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
n=29
for shape in ['fixed4','common','tuple','borrowed']:
    prep=subprocess.run([sys.executable,str(E/'NEE_prepare_shape.py'),shape],capture_output=True,text=True)
    if prep.returncode:raise SystemExit(prep.stdout+prep.stderr)
    for test in ['native_weak','unimplied','frame_violation']:
        a=f'NEE_K{n:03}';n+=1
        assert not (E/a).exists(),'Never rerun a completed/submitted attempt'
        harness='pool_v1::payment_relation::NEE_shape::'+test
        rc=subprocess.run([sys.executable,str(E/'NEE_kani_run.py'),a,'kani',harness]).returncode
        if not (E/a/'receipt.json').exists():raise SystemExit('Missing receipt: recover, never resubmit')
        receipt=json.loads((E/a/'receipt.json').read_text())
        log=(E/a/'stdout.log').read_text()
        with (E/'NEE_SHAPE_SEQUENCE.jsonl').open('a') as f:f.write(json.dumps(dict(shape=shape,test=test,attempt=a,exit=receipt['exit_status'],semantic_success='VERIFICATION:- SUCCESSFUL' in log,semantic_failure='VERIFICATION:- FAILED' in log and 'Failed Checks:' in log,timeout='CBMC timed out' in log))+'\n')
        if 'CBMC timed out' in log:
            print('Shape remains OPEN after timeout; next test is a different independent interface property, never a rerun.',flush=True)
assert n==41
