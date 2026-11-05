from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_native_prepare import decoder
number=14
startfrom=int(sys.argv[1]) if len(sys.argv)>1 else 14
for fun in ['decode_terminal_master_box_v1','decode_master_account','decode_terminal_checkpoint_box_v1','decode_retained_pair_forest_checkpoint_account_v1','decode_terminal_lane_box_v1','decode_lane_account_from_program_invariant_v1']:
 for case in range(5 if 'lane' in fun else 6):
  for neg in [False,True]:
   a=f'NIE_K{number:03}';number+=1
   if number-1<startfrom:continue
   decoder(fun,case,neg)
   with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIE_kani_run.py'),a,'pair_forest::NIE_native::association'],stdout=f,stderr=subprocess.STDOUT)
   p=E/a/'receipt.json'
   if not p.exists():raise SystemExit('Client failure; details retained: '+a)
   x=json.loads(p.read_text());s=(p.parent/'stdout.log').read_text()
   summary=dict(attempt=a,function=fun,case=case,expected='FAIL' if neg else 'PASS',exit=x['exit_status'],success='SUCCESSFUL' in s,timeout='timed out' in s,compiler='could not compile' in s,wall=x['wall_seconds'])
   with (E/'NIE_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
   print(json.dumps(summary),flush=True)
   if summary['timeout'] or summary['compiler'] or summary['success']==neg:raise SystemExit('Review required; no unchanged rerun')
