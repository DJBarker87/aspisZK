from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;python=sys.executable
cfg=lambda a,m:subprocess.run([python,str(E/'NLU_config.py'),a,m],check=True)
def run(a):
 p=E/a/'receipt.json'
 if p.exists():return json.loads(p.read_text())['exit_status']
 status=subprocess.run([python,str(E/'NLU_run.py'),a]).returncode
 assert p.exists(),'Missing receipt: recover read-only; never resubmit a submitted target'
 return status
if not (E/'NLU_MODULES.json').exists():subprocess.run([python,str(E/'NLU_prepare_audit.py')],check=True)
a='NLU_L111';cfg(a,'NLU_COMBINED_IMPORT')
if run(a):sys.exit(1)
for n,m in [(112,'NLU_Driver'),(113,'NLU_ProofDriver')]:
 a=f'NLU_L{n:03}';cfg(a,m);p=E/(a+'.json');x=json.loads(p.read_text());x['command']+=['-c','NLU_native/'+m+'.c'];x['collect']=['NLU_native/'+m+'.c'];p.write_text(json.dumps(x))
 if run(a):sys.exit(1)
for n,m in [(114,'NLU_Driver'),(115,'NLU_ProofDriver')]:
 a=f'NLU_L{n:03}';x=json.loads((E/'NLU_L112.json').read_text());x={k:v for k,v in x.items() if k not in ['deps_fingerprint','source_revision','source_tree_dirty']}
 x.update(attempt=a,kind='link',module=m,sources=['NLU_native/'+m+'.c','NLU_native/NFA_WALKER.c','NLU_native/NFA_MemoryLimit.c'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NLU_native/'+m,'NLU_native/'+m+'.c','NLU_native/NFA_WALKER.c','NLU_native/NFA_MemoryLimit.c'],collect=[],expected_time='Optimized C compilation/link of one pinned unchanged audit driver')
 (E/(a+'.json')).write_text(json.dumps(x))
 if run(a):sys.exit(1)
for n,mode in [(116,'fixtures'),(117,'scan')]:
 a=f'NLU_L{n:03}';subprocess.run([python,str(E/'NLU_audit_config.py'),a,mode],check=True)
 if run(a):sys.exit(1)
verdicts=[]
for n in range(118,149):
 a=f'NLU_L{n:03}';mode='proof'+str(n-118);subprocess.run([python,str(E/'NLU_audit_config.py'),a,mode],check=True)
 status=run(a);verdicts.append(dict(attempt=a,group=mode,exit=status))
 (E/'NLU_RAW_GROUP_STATUSES.json').write_text(json.dumps(verdicts,indent=1))
a='NLU_L149';subprocess.run([python,str(E/'NLU_audit_config.py'),a,'close'],check=True)
sys.exit(run(a))
