from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(39, 'empty_contract', 0, None), (40, 'empty_contract', 1, 'NJZ_INVERT'), (41, 'default_contract', 0, None), (42, 'default_contract', 1, 'NJZ_INVERT'), (43, 'tree_fidelity_contract', 0, None), (44, 'tree_fidelity_contract', 1, 'NJZ_INVERSE_ENSURES'), (45, 'tree_fidelity_real', 0, None), (46, 'tree_fidelity_unimplied', 1, None), (47, 'tree_fidelity_modifies_check', 0, None), (48, 'tree_fidelity_modifies_check', 1, 'NJZ_BAD_MODIFIES')]
for n,name,expected,flag in jobs:
 a=f'NJZ_K{n:03d}';env=dict(os.environ)
 if flag:env[flag]='1'
 with (E/(a+'-summary.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NJZ_run.py'),a,'kani','verifier::NJZ_native::'+name],env=env,stdout=out,stderr=subprocess.STDOUT)
 print(a,name,'exit',r.returncode,flush=True)
 p=E/a/'stdout.log'
 if r.returncode!=expected or not p.exists() or 'timed out' in p.read_text() or ('error[' in p.read_text()):sys.exit(1)
