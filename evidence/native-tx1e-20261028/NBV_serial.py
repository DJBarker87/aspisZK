from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBV_host as h
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 a=f'NBV_K{n:03}';assert not (E/a/'receipt.json').exists()
 r=subprocess.run([sys.executable,str(E/'NBV_host.py'),a]);assert r.returncode==0
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 print('TERMINAL',a,rc['exit_status'],flush=True)
 if 'VERIFICATION:- FAILED' in out and n not in [2,8,14,15,17,19,21]:raise SystemExit('FINDING: inspect failed property before continuing')
 if 'TIMEOUT' in out or rc['exit_status']==124:
  r=h.remote_py(f'''from pathlib import Path
import json
p=Path({(h.B+'/NBV_tmp')!r});out=[]
for x in p.rglob('*'):
 if x.is_file() and (x.name.startswith('external-sat') or x.name.startswith('smt2_dec_problem')):out.append(dict(path=str(x),size=x.stat().st_size));x.unlink()
print(json.dumps(out))''');assert r.returncode==0
  (E/(a+'-timeout-cleanup.json')).write_text(r.stdout)
