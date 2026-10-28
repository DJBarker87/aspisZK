from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBV_host as h
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 a=f'NBV_K{n:03}';assert not (E/a/'receipt.json').exists()
 if json.loads((E/(a+'.json')).read_text()).get('deferred'):raise SystemExit('Deferred before admission; no scope launched')
 r=subprocess.run([sys.executable,str(E/'NBV_host.py'),a]);assert r.returncode==0
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 print('TERMINAL',a,rc['exit_status'],flush=True)
 timed='timed out' in out.lower() or rc['exit_status']==124
 if rc['exit_status']!=0 and not timed and 'VERIFICATION:- FAILED' not in out:raise SystemExit('Pre-proof failure: inspect and repair own input')
 if 'VERIFICATION:- FAILED' in out and not timed and n not in [2,8,14,15,17,19,21,29,31,33,35,37,41,43,45,47,49,50]:raise SystemExit('FINDING: inspect failed property before continuing')
 if timed:
  r=h.remote_py(f'''from pathlib import Path
import json
p=Path({(h.B+'/NBV_tmp')!r});out=[]
for x in p.rglob('*'):
 if x.is_file() and (x.name.startswith('external-sat') or x.name.startswith('smt2_dec_problem')):out.append(dict(path=str(x),size=x.stat().st_size));x.unlink()
print(json.dumps(out))''');assert r.returncode==0
  (E/(a+'-timeout-cleanup.json')).write_text(r.stdout)
