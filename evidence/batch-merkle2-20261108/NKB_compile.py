from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent
n=int(sys.argv[1]); module=sys.argv[2];a=f'NKB_L{n:03d}'
assert module.startswith('NKB_')
x=dict(attempt=a,kind='lean',module=module,sources=[f'NKB_lean/{module}.lean'],upload=[f'NKB_lean/{module}.lean'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o',f'NKB_objects/{module}.olean',f'NKB_lean/{module}.lean'],timeout=180,source_revision='',expected_time='Focused single module elaboration',env=json.loads((E/'NKB_ENV.json').read_text()))
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NKB_run.py'),a]);raise SystemExit(r.returncode)
