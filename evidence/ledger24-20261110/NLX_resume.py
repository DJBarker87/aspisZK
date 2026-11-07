"""Run only changed smaller aggregations after the retained L023 timeout."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
plan=json.loads((E/'NLX_AUDIT_GROUPS.json').read_text());manifest=json.loads((E/'NLX_AUDIT_ROOTS.json').read_text())
for i,target in plan['remaining_schedule']:
 a=f'NLX_L{i:03}';assert not(E/a).exists(),'Never resubmit '+a
 r=subprocess.run([sys.executable,str(E/'NLX_run.py'),a,'audit',target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 if r.returncode:
  q=E/a/'receipt.json'
  if not q.exists()or json.loads(q.read_text())['exit_status']!=1:print(a+' STOP inspect retained scope verdict',flush=True);sys.exit(r.returncode)
  for row in plan['required']:
   if row['mode']!=target:continue
   p=E/'NLX_audit'/target/('proof'+str(row['group'])+'.json');assert p.exists(),'Missing per-child receipt, never treat timeout as collector disagreement'
   x=json.loads(p.read_text());group=manifest['groups'][row['group']]
   assert[r['root']for r in x['results']]==group
   assert all(set(z['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}and(z['equal']or z['root']in {'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'})for z in x['results'])
  print(a+' raw standard;inherited collector finding retained',flush=True)
 else:print(a+' '+target+' PASS',flush=True)
