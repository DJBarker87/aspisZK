from pathlib import Path
import subprocess,sys,time,json
E=Path(__file__).resolve().parent
while not (E/'NBZ_K074/receipt.json').exists():time.sleep(5)
for a,name,src in [('NBZ_SYNC008','NBZ_store','/tmp/NBZ_store.rs'),('NBZ_SYNC009','NBZ_dictionary','/tmp/NBZ_dictionary_generated.rs')]:
 r=subprocess.run([sys.executable,str(E/'NBZ_sync.py'),a,name,src]);assert r.returncode==0
rows=[];n=75
for filename in ['NBZ_STORE_PLAN.json','NBZ_DICTIONARY_PLAN.json']:
 predecessor=None
 for original in json.loads((E/filename).read_text()):
  row=dict(original,attempt=f'NBZ_K{n:03d}',sources=['NBZ_windows.rs','NBZ_steps.rs','NBZ_decoders.rs','NBZ_dots.rs','NBZ_observer.rs','NBZ_store.rs','NBZ_dictionary.rs']);n+=1
  if row['negative']:row['positive']=predecessor
  else:predecessor=row['attempt']
  rows.append(row)
(E/'NBZ_LAST_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NBZ_gate_queue.py'),str(E/'NBZ_LAST_PLAN.json')]);sys.exit(r.returncode)
