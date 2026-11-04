from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
for n in range(1,23):
 for bad in [False,True]:
  number=39+2*(n-1)+int(bad)
  if number==39:continue
  a=f'NET_K{number:03}';h=f'verifier::NET_prefix::NET_prefix_{n:02}'
  subprocess.run([sys.executable,str(E/'NET_kani.py'),a,h]+(['NET_bad_reply'] if bad else []))
  p=E/a/'receipt.json';assert p.exists(),'No terminal receipt; recover only'
  rc=json.loads(p.read_text());text=(p.parent/'stdout.log').read_text()
  assert rc['exit_status']==int(bad) and ('VERIFICATION:- FAILED' if bad else 'VERIFICATION:- SUCCESSFUL') in text,'Unexpected result; stop this shape and isolate'
  assert 'timed out' not in text.lower()
