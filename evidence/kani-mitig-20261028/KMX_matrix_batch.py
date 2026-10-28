from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for i,pattern in enumerate(sys.argv[2:],int(sys.argv[1])):
 a=f'KMX_K{i:03}';print('START',a,pattern,flush=True)
 subprocess.run([sys.executable,str(E/'KMX_run.py'),a,'kani','python3','KMX_gate.py',a,pattern,'--cbmc-args','--unwinding-assertions'],check=True)
 subprocess.run([sys.executable,str(E/'KMX_report.py')],check=True)
 rows=[r for r in json.loads((E/'KMX_RESULTS.json').read_text()) if r['attempt']==a]
 assert rows,a
 print('DONE',a,[(r['harness'],r['result'],r['unwind_failure']) for r in rows],flush=True)
 if any(r['unwind_failure'] or r['result']=='INCOMPLETE' for r in rows):raise SystemExit('STOP invalid bound or incomplete result')

 if any(r['result']=='TIMEOUT' for r in rows):
  import KMX_host as h
  x=h.remote_py('from pathlib import Path\nimport json\nb=Path('+repr(h.B)+')\nps=list((b/"KMX_tmp").rglob("external-sat*"))+list((b/"KMX_tmp").rglob("smt2_dec_problem*"))\nfor p in ps:\n if p.is_file():p.unlink()\nprint(json.dumps(dict(removed=[str(p) for p in ps])))')
  assert x.returncode==0,x.stderr
  (E/(a+'-solver-cleanup.json')).write_text(x.stdout)
