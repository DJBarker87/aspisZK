from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent
n=int(sys.argv[1]); module=sys.argv[2];a=f'NJV_L{n:03d}'
assert module.startswith('NJV_')
x=dict(attempt=a,kind='lean',module=module,sources=[f'NJV_lean/{module}.lean'],upload=[f'NJV_lean/{module}.lean'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o',f'NJV_objects/{module}.olean',f'NJV_lean/{module}.lean'],timeout=180,source_revision='',expected_time='Focused single module elaboration',env=json.loads((E/'NJV_ENV.json').read_text()))
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
r=subprocess.run([sys.executable,str(E/'NJV_run.py'),a]);raise SystemExit(r.returncode)
