from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);ids=sys.argv[2:]
plan=json.loads((E/'KMX_ALL_REPLAY_PLAN.json').read_text())
for i,original in enumerate(ids,start):
 p=next(p for p in plan if p['original']==original);a=f'KMX_K{i:03}'
 pattern=('@statement:' if p['crate']=='aspis-statement' else '')+p['harness']
 print('START',a,original,flush=True)
 subprocess.run([sys.executable,str(E/'KMX_run.py'),a,'kani','python3','KMX_gate.py',a,pattern,'-Z','concrete-playback','--concrete-playback','print','--cbmc-args','--unwinding-assertions'],check=True)
 subprocess.run([sys.executable,str(E/'KMX_report.py')],check=True)
 rows=json.loads((E/'KMX_RESULTS.json').read_text());hits=[r for r in rows if r['attempt']==a]
 assert len(hits)==1,(a,hits)
 r=hits[0];print('DONE',a,original,r['result'],flush=True)
 if r['result']=='FAIL':raise SystemExit('STOP property failure: capture native replay before proceeding')
 if r['result']=='INCOMPLETE':raise SystemExit('STOP incomplete verification')
 if r['result']=='TIMEOUT':
  import KMX_host as h
  x=h.remote_py('from pathlib import Path\nimport hashlib,json\nb=Path('+repr(h.B)+')\nlock=hashlib.sha256((b/"KMX_src/Cargo.lock").read_bytes()).hexdigest()\nassert lock=="5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef"\nps=list((b/"KMX_tmp").rglob("external-sat*"))+list((b/"KMX_tmp").rglob("smt2_dec_problem*"))\nfor p in ps:\n if p.is_file():p.unlink()\nprint(json.dumps(dict(lock_after=lock,removed=[str(p) for p in ps])))')
  assert x.returncode==0,x.stderr
  (E/(a+'-post-timeout.json')).write_text(x.stdout)
