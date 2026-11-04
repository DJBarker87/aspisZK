from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
modes=[*(('field-'+n,False) for n in ['kind','master','selected','lane','nullifier','index','root','frontier']),('window',True),('window-byte',False),('window-frame',False),('box',True),('box-value',False),('box-allocation',False)]
for n,(mode,expected) in enumerate(modes,40):
 a=f'NFO_K{n:03}'
 if (E/a/'receipt.json').exists():continue
 subprocess.run([sys.executable,str(E/'NFO_extra_native.py'),mode],check=True)
 r=subprocess.run([sys.executable,str(E/'NFO_kani_run.py'),a],capture_output=True,text=True);print(a,mode,r.returncode,flush=True)
 if not (E/a/'receipt.json').exists():print(r.stdout+r.stderr);sys.exit('STOP missing receipt')
 d=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 assert d['exit_status']==(0 if expected else 1),(a,'wrong exit',r.stdout+r.stderr)
 assert ('VERIFICATION:- SUCCESSFUL' if expected else 'VERIFICATION:- FAILED') in log,(a,'no verdict')
 assert 'Failed Checks: unwinding' not in log and 'TIMEOUT' not in log and 'Timed out' not in log,(a,'excluded shape; inspect first')
 with (E/'NFO_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,mode=mode,expected_success=expected,matched=True))+'\n')
