import subprocess,pathlib,sys
D='/home/dombarker/project-offloads/codex-pv-fscan-20261028/'
jobs=[['classify-project-'+n,'finite-validation','python3',D+'classify-project-native.py',n] for n in ['circle','sampler','weights','rows']]
for j in jobs:
 if pathlib.Path('evidence/pv-fscan-20261028',j[0],'receipt.json').exists():continue
 r=subprocess.run(['python3','tools/pv-fscan-20261028/scope.py',*j],capture_output=True,text=True)
 pathlib.Path('evidence/pv-fscan-20261028',j[0]+'-dispatch.log').write_text(r.stdout+r.stderr)
 print(j[0],r.returncode,flush=True)
 if r.returncode:print((r.stdout+r.stderr)[-1500:],flush=True);sys.exit(r.returncode)
