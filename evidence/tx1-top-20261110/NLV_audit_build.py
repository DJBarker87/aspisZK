from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-tx1-top-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,mode=sys.argv[1:]
if mode in ['Driver','ProofDriver']:
 m='NLV_'+mode;subprocess.run([sys.executable,str(E/'NLV_config.py'),a,m],check=True);x=json.loads((E/(a+'.json')).read_text());x['command'][x['command'].index('-o'):x['command'].index('-o')]=['-c','NLV_native/'+m+'.c'];x['collect']=['NLV_native/'+m+'.c'];x['expected_time']='Compile unchanged audit driver with own manifest names; native C output'
elif mode=='link':
 x=json.loads((E/'NLV_L097.json').read_text());x.update(attempt=a,kind='link',module='NLV_Driver',sources=['NLV_generated/NLV_Driver.lean','NLV_generated/NLV_ProofDriver.lean','NLV_link.py','NLV_native/NLV_Driver.c','NLV_native/NLV_ProofDriver.c','NLV_native/NFA_WALKER.c','NLV_native/NFA_MemoryLimit.c'],command=['python3','NLV_link.py'],collect=['NLV_AUDIT_BINARY_PINS.json'],expected_time='Optimized link of unchanged raw ax2 and NFX drivers; one capped scope')
else:raise SystemExit(mode)
(E/(a+'.json')).write_text(json.dumps(x))
