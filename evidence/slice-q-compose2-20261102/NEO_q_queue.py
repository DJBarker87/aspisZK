"""Five independent representation roots, serial exact paired controls."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for number,name in enumerate(['q_limbs','q_from_limbs','q_from_wide','limbs_of','checked_q']):
 for control in [False,True]:
  n=24+2*number+int(control);a=f'NEO_K{n:03}'
  command=[sys.executable,str(E/'NEO_kani.py'),a,'fast_pairing::canonical::NEO_q::'+name]+(['NEO_wrong_q'] if control else [])
  subprocess.run(command)
  p=E/a/'receipt.json';assert p.exists(),'no terminal receipt; stop'
  d=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
  assert d['exit_status']==int(control) and ('VERIFICATION:- FAILED' if control else 'VERIFICATION:- SUCCESSFUL') in log,'unexpected verdict: inspect, do not launch the next shape'
  if control:assert '** 1 of ' in log,'control failed another check'
