#!/usr/bin/env python3
"""Sequential remaining changed-target checks; stop on any failed receipt."""
from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
for point in range(1,6):
 a=f's1-native-prepared-claim-v{4+2*point}';b=f's1-native-prepared-claim-v{5+2*point}'
 harness=f'verifier::proofs::prepared_new_claim_point_{point}'
 for attempt,extra in [(a,[]),(b,['--verify','--predecessor',a])]:
  subprocess.run([sys.executable,str(T/'run.py'),'--attempt',attempt,'--harness',harness,*extra],cwd=R,check=True)
  receipt=json.loads((E/attempt/'receipt.json').read_text())
  assert receipt['exit_status']==0 and receipt['watchdog_stop'] is None,(point,attempt,receipt['exit_status'],receipt['watchdog_stop'])
 print(json.dumps(dict(completed_claim_error_point=point,accepted_attempt=b)),flush=True)
