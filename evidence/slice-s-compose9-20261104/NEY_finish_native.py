"""Final repair after K147 private-module compile error; remaining slots only."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(n,'scalar',[shape,mode],'NEY_SCALAR_CURRENT.json','r1_pool_adapter::NEY_scalar::scalar',True) for n,shape,mode in [(148,'limbs','positive'),(149,'limbs','value'),(150,'tag','positive')]]
for n,g,args,current,harness,program in jobs:
 a=f'NEY_K{n:03}';assert not (E/a).exists()
 subprocess.run([sys.executable,str(E/('NEY_prepare_'+g+'.py')),*args],check=True)
 (E/(a+'-shape.json')).write_bytes((E/current).read_bytes())
 subprocess.run([sys.executable,str(E/('NEY_program_kani_run.py' if program else 'NEY_kani_run.py')),a,'kani',harness],check=False)
 assert (E/a/'receipt.json').exists(),'Recover submitted job read-only'
 log=(E/a/'stdout.log').read_text();rc=json.loads((E/a/'receipt.json').read_text())['exit_status'];print(a,rc,flush=True)
 if 'timed out' in log or rc==124:raise SystemExit('Review timeout before any next scope')
 if not any(s in log for s in ['VERIFICATION:- SUCCESSFUL','VERIFICATION:- FAILED']):raise SystemExit('Repair compile/gate failure before next scope')
