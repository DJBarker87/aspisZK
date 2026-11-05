from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
families=['arguments','place','profile','release','program','kind','pool','deployment_domain','anchor_sequence','anchor_root','nullifier','asset_id','recipient_commitment','change_commitment','amount','destination_token_account']
index=12
for family in families:
 for mode in ['positive','negative']:
  a=f'NHC_K{index:03}';index+=1
  r=subprocess.run([sys.executable,str(E/'NHC_request_box.py'),family,mode],capture_output=True,text=True)
  if r.returncode:print('generator failed',family,mode,r.stderr[-1000:]);sys.exit(2)
  r=subprocess.run([sys.executable,str(E/'NHC_kani_run.py'),a,'pair_forest::NHC_RequestBox::association'],capture_output=True,text=True)
  (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
  raw=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
  timeout='CBMC timed out.' in raw or ('receipt.json' in str(r.stderr) and r.returncode)
  good=('VERIFICATION:- SUCCESSFUL' in raw) if mode=='positive' else ('VERIFICATION:- FAILED' in raw and ('Failed Checks:' in raw))
  with(E/'NHC_REQUEST_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,family=family,mode=mode,exit=r.returncode,expected=good,timeout=timeout))+'\n')
  print(a,family,mode,r.returncode,'expected',good,flush=True)
  if not good:
   if timeout and mode=='positive':break
   print('Review unexpected result; no further dependent launches',flush=True);sys.exit(3)
