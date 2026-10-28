from pathlib import Path
import subprocess,sys,time,json
E=Path(__file__).resolve().parent
# Do not mutate any source until the currently submitted native queue is done.
while not ((E/'NBZ_K052/receipt.json').exists() or (E/'NBZ_K052-skipped.json').exists()):time.sleep(5)
for a,name,src in [('NBZ_SYNC005','NBZ_decoders','/tmp/NBZ_decoders_generated.rs'),('NBZ_SYNC006','NBZ_dots','/tmp/NBZ_dots.rs'),('NBZ_SYNC007','NBZ_observer','/tmp/NBZ_observer_generated.rs')]:
 r=subprocess.run([sys.executable,str(E/'NBZ_sync.py'),a,name,src]);assert r.returncode==0
rows=[];n=53
for filename in ['NBZ_DECODER_PLAN.json','NBZ_DOT_PLAN.json']:
 predecessor=None
 for original in json.loads((E/filename).read_text()):
  row=dict(original,attempt=f'NBZ_K{n:03d}',sources=['NBZ_windows.rs','NBZ_steps.rs','NBZ_decoders.rs','NBZ_dots.rs','NBZ_observer.rs']);n+=1
  if row['negative']:row['positive']=predecessor
  else:predecessor=row['attempt']
  rows.append(row)
for original in json.loads((E/'NBZ_OBSERVER_PLAN.json').read_text()):
 rows.append(dict(original,attempt=f'NBZ_K{n:03d}',sources=['NBZ_windows.rs','NBZ_steps.rs','NBZ_decoders.rs','NBZ_dots.rs','NBZ_observer.rs']));n+=1
(E/'NBZ_FOLLOWUP_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NBZ_gate_queue.py'),str(E/'NBZ_FOLLOWUP_PLAN.json')]);sys.exit(r.returncode)
