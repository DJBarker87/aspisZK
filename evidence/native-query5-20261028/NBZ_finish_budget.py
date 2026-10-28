"""Use remaining actual Kani slots on independent unresolved members."""
from pathlib import Path
import subprocess,sys,time,json
E=Path(__file__).resolve().parent
while not ((E/'NBZ_K102/receipt.json').exists() or (E/'NBZ_K102-skipped.json').exists()):
 if len(list(E.glob('NBZ_K[0-9][0-9][0-9].json')))>=90:raise SystemExit(0)
 time.sleep(5)
def used():return len(list(E.glob('NBZ_K[0-9][0-9][0-9].json')))
if used()>=90:raise SystemExit(0)
for a,name,src in [('NBZ_SYNC010','NBZ_reject','/tmp/NBZ_reject_generated.rs'),('NBZ_SYNC011','NBZ_rescue','/tmp/NBZ_rescue.rs'),('NBZ_SYNC012','NBZ_extra_controls','/tmp/NBZ_extra_controls_generated.rs')]:
 r=subprocess.run([sys.executable,str(E/'NBZ_sync.py'),a,name,src]);assert r.returncode==0
sources=['NBZ_windows.rs','NBZ_steps.rs','NBZ_decoders.rs','NBZ_dots.rs','NBZ_observer.rs','NBZ_store.rs','NBZ_dictionary.rs','NBZ_reject.rs','NBZ_rescue.rs','NBZ_extra_controls.rs']
next_id=103
allrows=[]
def run_rows(originals):
 global next_id
 rows=[];predecessor=None
 for original in originals:
  row=dict(original,attempt=f'NBZ_K{next_id:03d}',sources=sources);next_id+=1
  if row.get('negative') and predecessor:row['positive']=predecessor
  elif not row.get('negative'):predecessor=row['attempt']
  rows.append(row)
 allrows.extend(rows);(E/'NBZ_BUDGET_PLAN.json').write_text(json.dumps(allrows,indent=2)+'\n')
 p=E/(rows[0]['attempt']+'-queue.json');p.write_text(json.dumps(rows,indent=2)+'\n')
 r=subprocess.run([sys.executable,str(E/'NBZ_gate_queue.py'),str(p)])
 if r.returncode and used()<90:raise SystemExit(r.returncode)
 return rows
# Attempt both original native rejection contexts with scalar setup/full carriers.
reject=json.loads((E/'NBZ_REJECT_PLAN.json').read_text())
for start in [0,2]:
 if 90-used()>=2:run_rows(reject[start:start+2])
# Split K065 into a single arbitrary coordinate; if it times out, isolate
# the eight literal constant-index source sites, never replaying its shape.
rescue=json.loads((E/'NBZ_RESCUE_PLAN.json').read_text())
if 90-used()>=2:
 first=run_rows(rescue[:2]);receipt=json.loads((E/first[0]['attempt']/'receipt.json').read_text())
 if receipt['exit_status']!=0:
  for start in range(2,len(rescue),2):
   if 90-used()<2:break
   run_rows(rescue[start:start+2])
# Restore additional inherited local NBB cuts with their exact false-value
# controls. These can legitimately consume a final single available slot.
for original in json.loads((E/'NBZ_EXTRA_PLAN.json').read_text()):
 if used()>=90:break
 run_rows([original])
if used()<90:
 r=subprocess.run([sys.executable,str(E/'NBZ_sync.py'),'NBZ_SYNC013','NBZ_observer_controls','/tmp/NBZ_observer_controls.rs']);assert r.returncode==0
 sources.append('NBZ_observer_controls.rs')
 for original in json.loads((E/'NBZ_OBSERVER_CONTROLS.json').read_text()):
  if used()>=90:break
  run_rows([original])
(E/'NBZ_BUDGET_DISPOSITION.json').write_text(json.dumps(dict(actual_kani_configurations=used(),limit=90,remaining=90-used()),indent=2)+'\n')
