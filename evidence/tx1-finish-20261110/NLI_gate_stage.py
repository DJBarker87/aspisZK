"""Sequential owned gate driver; each target still has separate admission/cap/receipt."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
python=sys.executable
run=lambda a:subprocess.run([python,str(E/'NLI_run.py'),a]).returncode
for n,m in [(102,'NLI_Driver'),(103,'NLI_ProofDriver')]:
 a=f'NLI_L{n:03}';subprocess.run([python,str(E/'NLI_config.py'),a,m],check=True)
 p=E/(a+'.json');d=json.loads(p.read_text());d['command']+=['-c','NLI_native/'+m+'.c'];d['collect']=['NLI_native/'+m+'.c'];p.write_text(json.dumps(d))
 if run(a):sys.exit(1)
for n,m in [(104,'NLI_Driver'),(105,'NLI_ProofDriver')]:
 a=f'NLI_L{n:03}';base=json.loads((E/'NLI_L102.json').read_text());d={k:v for k,v in base.items()if k not in ['deps_fingerprint','source_revision','source_tree_dirty']}
 d.update(attempt=a,kind='link',module=m,sources=['NLI_native/'+m+'.c','NLI_native/NFA_WALKER.c','NLI_native/NFA_MemoryLimit.c'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NLI_native/'+m,'NLI_native/'+m+'.c','NLI_native/NFA_WALKER.c','NLI_native/NFA_MemoryLimit.c'],collect=[])
 (E/(a+'.json')).write_text(json.dumps(d))
 if run(a):sys.exit(1)
for n,mode in [(106,'fixtures'),(107,'scan')]:
 a=f'NLI_L{n:03}';subprocess.run([python,str(E/'NLI_audit_config.py'),a,mode],check=True);rc=run(a)
 if mode=='scan'and rc:sys.exit(1)
