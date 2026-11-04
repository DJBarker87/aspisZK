"""Serial accepted-cut windows; stop for review on any unexpected result."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
plan=[('argument','place324'),('positive','accounts'),('account','accounts'),('positive','hints'),('reply','hints')]
fields=['profile','release','program','kind']+['field:'+x for x in ['pool','deployment_domain','anchor_sequence','anchor_root','nullifier','asset_id','recipient_commitment','change_commitment','amount','destination_token_account']]
plan += [(mode,field) for field in fields for mode in ['positive','reply']]
for i,(mode,family) in enumerate(plan,28):
 a=f'NGG_K{i:03d}'
 subprocess.run([sys.executable,str(E/'NGG_decode_cut.py'),mode,family,'accepted'],check=True)
 r=subprocess.run([sys.executable,str(E/'NGG_kani_run.py'),a,'pair_forest::NGG_DecodeCut::association'],capture_output=True,text=True)
 print(a,mode,family,r.returncode,r.stdout.strip(),flush=True)
 log=E/a/'stdout.log'
 if not log.exists():print(r.stderr,flush=True);raise SystemExit('STOP missing terminal native receipt')
 out=log.read_text();expected=0 if mode=='positive' else 1
 if r.returncode!=expected or 'CBMC timed out.' in out or (mode!='positive' and 'VERIFICATION:- FAILED' not in out):
  print(out[-1500:],flush=True);raise SystemExit('STOP review native window; never rerun unchanged timeout')
