from pathlib import Path
import json,subprocess,sys
p=Path(__file__).resolve().parent
mapping=json.loads((p/'NLH_GATE_ATTEMPTS.json').read_text())
allowed={'AspisR1.NKR_ScheduleExt.transition','AspisR1.NHC_DecodeModel.decoder_error'}
for mode,a in mapping.items():
 if len(sys.argv)>1 and int(a[5:])<int(sys.argv[1]):continue
 r=subprocess.run(['python3',str(p/'NLH_run.py'),str(p/(a+'.json'))])
 if r.returncode:
  q=p/'NLH_audit'/mode/'receipt.json'
  if not(mode.startswith('proof')and q.exists()):sys.exit(r.returncode)
  row=json.loads(q.read_text());names={x['root']for x in row['collect_axioms_disagreements']}
  if not(row['exit_status']==1 and row['standard_only'] and names and names<=allowed):sys.exit(r.returncode)
  print(json.dumps(dict(attempt=a,raw_standard_only=True,original_exit=1,retained_collector_disagreements=sorted(names))),flush=True)
 print(json.dumps(dict(attempt=a,mode=mode,exit=r.returncode)),flush=True)
