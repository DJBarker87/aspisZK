from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
n=int(sys.argv[1]);module=sys.argv[2];a=f'NKI_L{n:03}'
env=json.loads((E/'NKI_PATH.json').read_text())
x=dict(attempt=a,kind='lean',module=module,sources=[module+'.lean','NKI_seed.py','NKI_PREDECESSOR_EXPORT.json','NKI_NKC_EXPORT.json'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','.','-o','NKI_objects/'+module+'.olean',module+'.lean'],timeout=180,expected_time='Focused symbolic proof or declaration inspection',env=env,collect=['NKI_SEED.json'])
(E/(a+'.json')).write_text(json.dumps(x))
