from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
lo,hi=map(int,sys.argv[1:3])
for job in json.loads((E/'NFV_NATIVE_PLAN.json').read_text()):
 a=job['attempt'];n=int(a[5:])
 if not lo<=n<=hi:continue
 assert not (E/a/'receipt.json').exists(),'never repeat a terminal attempt'
 if (E/'NFV_PAUSE').exists():raise SystemExit('Paused between terminal attempts')
 subprocess.run([sys.executable,str(E/job['generator']),*job['args']],check=True)
 current=json.loads((E/'NFV_CURRENT.json').read_text())['source']
 assert not any(json.loads(p.read_text()).get('source')==current for p in E.glob('NFV_K*-shape.json')),'never repeat an unchanged source'
 r=subprocess.run([sys.executable,str(E/'NFV_kani_run.py'),a,job['harness']],capture_output=True,text=True)
 p=E/a/'receipt.json'
 if not p.exists():print(r.stdout+r.stderr,flush=True);raise SystemExit('STOP missing terminal receipt; recover READ-ONLY')
 rc=json.loads(p.read_text());text=(E/a/'stdout.log').read_text();start=text.rfind('Failed Checks:')
 row=dict(**job,exit=rc['exit_status'],timeout='timed out' in text.lower(),unwind='unwinding assertion' in text,failed_check=text[start:text.index('\n\n',start)] if start>=0 and '\n\n' in text[start:] else '')
 with (E/'NFV_NATIVE_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps({k:v for k,v in row.items() if k!='failed_check'}),flush=True)
 if job['expected'] in ['PASS','intended-FAIL']:
  if row['timeout'] or row['unwind'] or rc['exit_status']!=(0 if job['expected']=='PASS' else 1):
   raise SystemExit('REVIEW terminal shape before continuing: '+a)
 if rc['exit_status'] not in [0,1,124]:raise SystemExit('REVIEW unexpected exit: '+a)
