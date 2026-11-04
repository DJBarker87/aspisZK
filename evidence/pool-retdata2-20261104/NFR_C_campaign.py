"""Strict serial C probes; review every unexpected verdict before proceeding."""
from pathlib import Path
import subprocess,json,sys,shutil
E=Path(__file__).resolve().parent
plan=[('carrier-byte',False),('carrier-pointer',False),('carrier-value',False),('getter',True)]+[(f'getter-field-{f}',False) for f in ['kind','master','selected','lane','nullifier','index','root','frontier']]+[('suffix',True)]+[(f'suffix-{s}',False) for s in ['byte','error','order','validator','lane','encoder','frame']]+[('direct',True)]+[(f'direct-{s}',False) for s in ['byte','error','field','call','pointer','length','frame','variant']]
assert len(plan)==29
start=int(sys.argv[1]) if len(sys.argv)>1 else 31
for offset,(mode,expected) in enumerate(plan):
 n=31+offset
 if n<start:continue
 a=f'NFR_K{n:03}';generator='NFR_C_direct.py' if mode.startswith('direct') else 'NFR_C_native.py'
 subprocess.run([sys.executable,str(E/generator),mode],check=True)
 shape=json.loads((E/'NFR_C_CURRENT.json').read_text())
 shutil.copyfile(E/'NFR_C_native.patch',E/'NFR_native.patch');shutil.copyfile(E/'NFR_C_CURRENT.json',E/'NFR_CURRENT.json')
 r=subprocess.run([sys.executable,str(E/'NFR_kani_run.py'),a,shape['harness']],capture_output=True,text=True)
 (E/(a+'-C-campaign.log')).write_text(r.stdout+r.stderr)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP no receipt '+a+' '+r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 verdict='VERIFICATION:- SUCCESSFUL' if expected else 'VERIFICATION:- FAILED'
 match=rc['exit_status']==(0 if expected else 1) and verdict in log and 'Failed Checks: unwinding' not in log and 'TIMEOUT' not in log and 'Timed out' not in log
 with (E/'NFR_C_CAMPAIGN.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,mode=mode,expected_success=expected,matched=match,exit=rc['exit_status']))+'\n')
 print(a,mode,rc['exit_status'],'matched' if match else 'REVIEW',flush=True)
 if not match:raise SystemExit('STOP unexpected result; isolate source/shape before next launch')
