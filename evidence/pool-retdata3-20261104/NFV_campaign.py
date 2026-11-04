from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
start=int(sys.argv[1]); kinds=sys.argv[2:] or ['meta','info']
n=start
for kind in kinds:
 for i in range(6):
  for control in ['positive','negative']:
   if (E/'NFV_PAUSE').exists():raise SystemExit('Paused between terminal attempts')
   a=f'NFV_K{n:03}';n+=1
   subprocess.run([sys.executable,str(E/'NFV_accounts.py'),kind,str(i),control],check=True)
   current=json.loads((E/'NFV_CURRENT.json').read_text())['source']
   if any(json.loads(p.read_text()).get('source')==current for p in E.glob('NFV_K*-shape.json')):
    n-=1;continue
   r=subprocess.run([sys.executable,str(E/'NFV_kani_run.py'),a],capture_output=True,text=True)
   rc=E/a/'receipt.json'
   if not rc.exists():print(r.stdout+r.stderr,flush=True);raise SystemExit('STOP missing terminal receipt')
   text=(E/a/'stdout.log').read_text();receipt=json.loads(rc.read_text())
   row=dict(attempt=a,kind=kind,index=i,control=control,exit=receipt['exit_status'],timeout='timed out' in text.lower() or receipt['exit_status']==124,unwind='unwinding assertion' in text,assertion_failure='assertion.' in text or 'assertion failed' in text)
   with (E/'NFV_ACCOUNT_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
   print(json.dumps(row),flush=True)
   if receipt['exit_status'] not in [0,1,124]:raise SystemExit('STOP unexpected terminal status')
