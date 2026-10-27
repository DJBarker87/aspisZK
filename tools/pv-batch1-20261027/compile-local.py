"""Sequential charged-attempt tally. Stops for review on any failed compile."""
from pathlib import Path
import subprocess,sys,json
E=Path('evidence/pv-batch1-20261027');P=E/'TALLY.json';H='/home/dombarker/project-offloads/codex-pv-batch1-20261027'
for module in sys.argv[1:]:
 t=json.loads(P.read_text());a=t['next_unused_id']
 assert a<53897 and t['lean_charged']<97 and module.startswith('PV_B1_')
 t['used_ids'].append(a);t['next_unused_id']=a+1;P.write_text(json.dumps(t,indent=2)+'\n')
 r=subprocess.run(['ssh','dombarker@100.108.41.90',f'cd {H} && python3 lean.py {a} {module}'],capture_output=True,text=True)
 (E/f'lean-{a}-launcher.log').write_text(r.stdout+r.stderr)
 summaries=[]
 for line in r.stdout.splitlines():
  try:
   x=json.loads(line)
   if isinstance(x,dict) and x.get('attempt')==a:summaries.append(x)
  except json.JSONDecodeError:pass
 if summaries:
  rec=summaries[-1]
  if rec['charged']:t['lean_charged']+=1
  t['stage']='focused Lean checks'
  P.write_text(json.dumps(t,indent=2)+'\n');print(json.dumps(rec),flush=True)
 elif r.returncode==78:print(a,'admission refused, charged0; wait180 seconds and use next ID',flush=True)
 else:
  print(r.stdout+r.stderr,flush=True);raise SystemExit('Unclassified launcher outcome: inspect receipt before continuing')
 if r.returncode:
  print((r.stdout+r.stderr)[-6000:],flush=True);raise SystemExit(r.returncode)
