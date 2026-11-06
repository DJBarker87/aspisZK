from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(57, 'fidelity_contract', 0, None), (58, 'fidelity_contract', 1, 'NJZ_INVERSE_ENSURES'), (59, 'fidelity_real', 0, None), (60, 'fidelity_unimplied', 1, None), (61, 'fidelity_modifies_check', 0, None), (62, 'fidelity_modifies_check', 1, 'NJZ_BAD_MODIFIES'), (63, 'tree_fidelity_contract', 0, None), (64, 'tree_fidelity_contract', 1, 'NJZ_INVERSE_ENSURES'), (65, 'tree_fidelity_real', 0, None), (66, 'tree_fidelity_unimplied', 1, None), (67, 'tree_fidelity_modifies_check', 0, None), (68, 'tree_fidelity_modifies_check', 1, 'NJZ_BAD_MODIFIES'), (69, 'result_fidelity_contract', 0, None), (70, 'result_fidelity_contract', 1, 'NJZ_INVERSE_ENSURES'), (71, 'result_fidelity_real', 0, None), (72, 'result_fidelity_unimplied', 1, None), (73, 'result_fidelity_modifies_check', 0, None), (74, 'result_fidelity_modifies_check', 1, 'NJZ_BAD_MODIFIES'), (75, 'roots_control', 0, None), (76, 'roots_control', 1, 'NJZ_INVERT')]
for n,name,expected,flag in jobs:
 a=f'NJZ_K{n:03d}';env=dict(os.environ)
 if flag:env[flag]='1'
 with (E/(a+'-summary.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NJZ_run.py'),a,'kani','verifier::NJZ_native::'+name],env=env,stdout=out,stderr=subprocess.STDOUT)
 print(a,name,'exit',r.returncode,flush=True)
 p=E/a/'stdout.log'
 if r.returncode!=expected or not p.exists() or 'timed out' in p.read_text() or ('error[' in p.read_text()):sys.exit(1)
