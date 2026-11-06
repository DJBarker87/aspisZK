from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for a in sys.argv[1:]:
 r=subprocess.run([sys.executable,str(E/'NKD_run.py'),a],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 if not (E/a/'receipt.json').is_file():raise RuntimeError('Recover before continuing '+a)
 x=json.loads((E/a/'receipt.json').read_text());raw=(E/a/'stdout.log').read_text()
 if x['kind']=='kani':
  cfg=json.loads((E/(a+'.json')).read_text());negative='NKD_invert' in cfg['env']['RUSTFLAGS']
  ok=x['exit_status']==int(negative) and ('VERIFICATION:- FAILED'if negative else 'VERIFICATION:- SUCCESSFUL')in raw
 else:ok=x['exit_status']==0
 print(a+' '+('PASS expected verdict'if ok else 'STOP unexpected verdict'),flush=True)
 if not ok:sys.exit(1)
