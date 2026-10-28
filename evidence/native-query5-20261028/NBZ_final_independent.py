from pathlib import Path
import json,subprocess,sys,time
E=Path(__file__).resolve().parent
while not (E/'NBZ_REDIRECT_ACK.json').exists():time.sleep(3)
(E/'NBZ_REDIRECT_REQUEST').unlink()
# The old executor exits before metadata/submission; no attempt is resubmitted.
r=subprocess.run([sys.executable,str(E/'NBZ_sync.py'),'NBZ_SYNC014','NBZ_coefficient','/tmp/NBZ_coefficient.rs']);assert r.returncode==0
sources=['NBZ_windows.rs','NBZ_steps.rs','NBZ_decoders.rs','NBZ_dots.rs','NBZ_observer.rs','NBZ_store.rs','NBZ_dictionary.rs','NBZ_reject.rs','NBZ_rescue.rs','NBZ_extra_controls.rs','NBZ_coefficient.rs']
rows=[dict(attempt='NBZ_K150',harness='verifier::candidate::NBZ_coefficient::NBZ_coefficient_read',sources=sources),dict(attempt='NBZ_K151',harness='verifier::candidate::NBZ_coefficient::NBZ_coefficient_read_negative',negative=True,positive='NBZ_K150',sources=sources)]
next_id=152
for original in json.loads((E/'NBZ_EXTRA_PLAN.json').read_text()):
 rows.append(dict(original,attempt=f'NBZ_K{next_id:03d}',sources=sources));next_id+=1
(E/'NBZ_FINAL_INDEPENDENT_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
for row in rows:
 if len(list(E.glob('NBZ_K[0-9][0-9][0-9].json')))>=90:break
 p=E/(row['attempt']+'-queue.json');p.write_text(json.dumps([row],indent=2)+'\n')
 r=subprocess.run([sys.executable,str(E/'NBZ_gate_queue.py'),str(p)]);assert r.returncode==0
used=len(list(E.glob('NBZ_K[0-9][0-9][0-9].json')))
if used<90:
 r=subprocess.run([sys.executable,str(E/'NBZ_sync.py'),'NBZ_SYNC015','NBZ_observer_controls','/tmp/NBZ_observer_controls.rs']);assert r.returncode==0
 sources.append('NBZ_observer_controls.rs')
 for original in json.loads((E/'NBZ_OBSERVER_CONTROLS.json').read_text()):
  if len(list(E.glob('NBZ_K[0-9][0-9][0-9].json')))>=90:break
  row=dict(original,attempt=f'NBZ_K{next_id:03d}',sources=sources);next_id+=1;p=E/(row['attempt']+'-queue.json');p.write_text(json.dumps([row],indent=2)+'\n');r=subprocess.run([sys.executable,str(E/'NBZ_gate_queue.py'),str(p)]);assert r.returncode==0
(E/'NBZ_BUDGET_DISPOSITION.json').write_text(json.dumps(dict(actual_kani_configurations=len(list(E.glob('NBZ_K[0-9][0-9][0-9].json'))),limit=90),indent=2)+'\n')
