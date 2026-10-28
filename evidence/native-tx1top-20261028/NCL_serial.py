from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCL_host as h
for number in range(int(sys.argv[1]),int(sys.argv[2])+1):
 a=f'NCL_K{number:03}'
 assert not (E/'NCL_ACTIVE.json').exists(),'Lean attempt still active'
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run([sys.executable,str(E/'NCL_host.py'),a])
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text());cfg=json.loads((E/(a+'.json')).read_text());log=(E/a/'stdout.log').read_text()
 # A timed-out pair is not continued in the same shape; review and split first.
 if any(x in log.lower() for x in ['cbmc timed out','harness timed out']) or rc['exit_status'] in [124,137]:
  print('REVIEW timeout; series stopped before paired shape',flush=True);break
 if not cfg['expected_negative'] and rc['exit_status']!=0:raise SystemExit('Positive failure: inspect before continuing')
 if cfg['expected_negative'] and (rc['exit_status']==0 or 'VERIFICATION:- FAILED' not in log):raise SystemExit('Control failed to fail at verification: inspect')
 print(a+' terminal; next independent configured gate',flush=True)
