from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
sys.path.insert(0,str(E));import NBY_host as h
for number in range(int(sys.argv[1]),int(sys.argv[2])+1):
 a=f'NBY_K{number:03}'
 if (E/a/'receipt.json').exists():continue
 if json.loads((E/(a+'.json')).read_text()).get('deferred'):raise SystemExit('Deferred before admission')
 r=subprocess.run([sys.executable,str(E/'NBY_host.py'),a])
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text())
 print(a,rc['exit_status'],flush=True)
 # On timeout, do not run an unchanged paired shape.
 if any(x in (E/a/'stdout.log').read_text().lower() for x in ['timeout','timed out']) or rc['exit_status'] in [124,137]:
  r=h.remote_py(f'''from pathlib import Path
import json
p=Path({(h.B+'/NBY_tmp')!r});out=[]
for x in p.rglob('*'):
 if x.is_file() and (x.name.startswith('external-sat') or x.name.startswith('smt2_dec_problem')):out.append(dict(path=str(x),size=x.stat().st_size));x.unlink()
print(json.dumps(out))''');assert r.returncode==0
  (E/(a+'-timeout-cleanup.json')).write_text(r.stdout)
  print('REVIEW timeout: stop series before any paired shape',flush=True);break
 cfg=json.loads((E/(a+'.json')).read_text())
 if not cfg.get('expected_negative') and rc['exit_status']!=0:raise SystemExit('Positive finding or pre-proof error: inspect before continuing')
 if cfg.get('expected_negative') and (rc['exit_status']==0 or 'VERIFICATION:- FAILED' not in (E/a/'stdout.log').read_text()):raise SystemExit('Control did not fail as required: inspect')
