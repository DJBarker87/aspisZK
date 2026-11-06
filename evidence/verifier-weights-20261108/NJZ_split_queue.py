from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(49, 'roots_store_contract', 0, None), (50, 'roots_store_contract', 1, 'NJZ_INVERT'), (51, 'result_fidelity_contract', 0, None), (52, 'result_fidelity_contract', 1, 'NJZ_INVERSE_ENSURES'), (53, 'result_fidelity_real', 0, None), (54, 'result_fidelity_unimplied', 1, None), (55, 'result_fidelity_modifies_check', 0, None), (56, 'result_fidelity_modifies_check', 1, 'NJZ_BAD_MODIFIES')]
for n,name,expected,flag in jobs:
 a=f'NJZ_K{n:03d}';env=dict(os.environ)
 if flag:env[flag]='1'
 with (E/(a+'-summary.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NJZ_run.py'),a,'kani','verifier::NJZ_native::'+name],env=env,stdout=out,stderr=subprocess.STDOUT)
 print(a,name,'exit',r.returncode,flush=True)
 p=E/a/'stdout.log'
 if r.returncode!=expected or not p.exists() or 'timed out' in p.read_text() or ('error[' in p.read_text()):sys.exit(1)
