"""Serial finite empty-root partitions; stop on first unexpected result."""
from pathlib import Path
import subprocess,json,sys
from NIH_config import write
E=Path(__file__).resolve().parent;target='pool_v1::pair_forest_semantic_terminal::NHU_native::NHU_transition_step'
for level in range(20):
 for negative in [False,True]:
  a='NIH_K'+str(18+2*level+int(negative)).zfill(3)
  flags='--cfg NIH_reject --cfg NIH_next --cfg NIH_error --cfg NIH_earlier --cfg NIH_level'+str(level)+(' --cfg NHU_invert' if negative else '')
  write(a,'kani',target,flags)
  with (E/(a+'-client.log')).open('w') as log:r=subprocess.run([sys.executable,str(E/'NIH_run.py'),a],stdout=log,stderr=subprocess.STDOUT)
  p=E/a/'receipt.json'
  if not p.exists():print(a,'NO RECEIPT; STOP',flush=True);sys.exit(1)
  rc=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text()
  expected=r.returncode==(1 if negative else 0) and ('VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL') in raw
  print(json.dumps(dict(attempt=a,level=level,negative=negative,exit=r.returncode,expected=expected,wall=rc['wall_seconds'],rss=rc['peak_rss_kib'])),flush=True)
  if not expected:sys.exit(1)
