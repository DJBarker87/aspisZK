from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;a,mode=sys.argv[1:];T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';env=json.loads((E/'NMO_ENV.json').read_text())
x=dict(attempt=a,kind='audit',module='NMO_COMBINED_IMPORT',sources=[],command=[],env=env,timeout=180,collect=[])
if mode in ['Driver','ProofDriver']:
 m='NMO_'+mode;x.update(kind='lean',module=m,sources=[m+'.lean'],command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','.','-o','NMO_objects/'+m+'.olean',m+'.lean','-c','NMO_native/'+m+'.c'],collect=['NMO_native/'+m+'.c'])
elif mode.startswith('link'):
 m='NMO_'+mode[4:];names=['NMO_native/'+m+'.c','NMO_native/NMO_Walker.c','NMO_native/NMO_MemoryLimit.c'];x.update(kind='link',module=m,sources=names,command=[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NMO_native/'+m,*names])
else:
 x.update(sources=['NMO_ProofDriver.lean','NMO_Driver.lean','NMO_audit_batch.py','NMO_AUDIT_ROOTS.json','NMO_AUDIT_MODULES.json','NMO_EXPECTED_IMPORTS.jsonl'],command=['python3','NMO_audit_batch.py',mode],collect_globs=['NMO_audit/'+mode+'/*'])
 if mode=='scan':x['collect']=['NMO_LOADED_scan.jsonl']
(E/(a+'.json')).write_text(json.dumps(x))
