from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n,mode in enumerate(['digest-arg','after-arg','validator-arg','reply','digest-error','after-error','validation-error','input-frame'],26):
 a=f'NFO_K{n:03}'
 if (E/a/'receipt.json').exists():continue
 subprocess.run([sys.executable,str(E/'NFO_decoder_native.py'),mode],check=True)
 r=subprocess.run([sys.executable,str(E/'NFO_kani_run.py'),a],capture_output=True,text=True)
 print(a,mode,'exit',r.returncode,flush=True)
 if not (E/a/'receipt.json').exists():print(r.stdout+r.stderr);sys.exit('STOP missing receipt')
 d=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 assert d['exit_status']==1 and 'VERIFICATION:- FAILED' in log,(a,'unexpected verdict',r.stdout+r.stderr)
 assert 'Failed Checks: unwinding' not in log and 'Timed out' not in log and 'TIMEOUT' not in log,(a,'excluded shape; review first')
 with (E/'NFO_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,mode='decoder-'+mode,expected_success=False,matched=True))+'\n')
