from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for offset,mode in enumerate([12,13,14,16,17,18]):
 for bad in [False,True]:
  number=29+offset*2+int(bad);a=f'NLJ_K{number:03}';h=f'r1_semantic::NLJ_native::observed_{mode:02}_'+('control' if bad else 'cut')
  subprocess.run([sys.executable,str(E/'NLJ_kconfig.py'),a,h],check=True)
  r=subprocess.run([sys.executable,str(E/'NLJ_run.py'),a]);p=E/a/'stdout.log';out=p.read_text() if p.exists() else ''
  good=(r.returncode==0 and 'VERIFICATION:- SUCCESSFUL' in out) if not bad else (r.returncode==1 and 'VERIFICATION:- FAILED' in out and 'assertion failed: !good' in out and 'timed out' not in out.lower())
  with (E/'NLJ_NATIVE_CLASSIFICATION.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,mode=mode,control=bad,expected_verdict=good))+'\n')
  if not good:sys.exit(1)
