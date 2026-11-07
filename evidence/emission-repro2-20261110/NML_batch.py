"""Sequential owned client orchestration; never wraps a launcher in flock."""
from pathlib import Path
import os,time,subprocess,json,sys
E=Path(__file__).resolve().parent
if len(sys.argv)>1:
 pid=int(sys.argv[1])
 while True:
  try:os.kill(pid,0)
  except ProcessLookupError:break
  time.sleep(10)
if not (E/'NML_E001'/'receipt.json').exists():raise SystemExit('First attempt has no terminal receipt: recover read-only before any next launch')
for a in ['NML_L001']+['NML_E%03d'%i for i in range(2,41)]:
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'NML_run.py'),a])
 if not (E/a/'receipt.json').exists():raise SystemExit('No terminal receipt: stop orchestration, recover read-only')
 with (E/'NML_BATCH.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,client_exit=r.returncode,receipt=str(E/a/'receipt.json')))+'\n')
