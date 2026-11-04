from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for k,bits in [(39,16),(40,8),(41,1)]:
 a=f'NGH_K{k:03}'
 r=subprocess.run(['python3',str(E/'NGH_run.py'),a,'kani','field::NGH_reference::actual_for_contract'],env=dict(os.environ,NGH_CORE='1',NGH_FOR='1',NGH_LOOP_DEBUG='1',NGH_BITS=str(bits)),capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError(r.stdout+r.stderr)
 x=json.loads(p.read_text());print(a,bits,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status']==0:
  print('Positive passed; stop for matching control and domain review',flush=True);break
 if 'CBMC timed out'not in(E/a/'stdout.log').read_text():raise RuntimeError('Non-timeout failure: inspect before proceeding')
