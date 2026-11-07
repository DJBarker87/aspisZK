"""One combined support campaign, followed by fixtures/NFX/raw ax2 and export."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;python=sys.executable
cfg=lambda a,m:subprocess.run([python,str(E/'NMC_config.py'),a,m],check=True)
def run(a):
 p=E/a/'receipt.json'
 if p.exists():return json.loads(p.read_text())['exit_status']
 status=subprocess.run([python,str(E/'NMC_run.py'),a]).returncode
 assert p.exists(),'Recover read-only; never resubmit a submitted target'
 return status
subprocess.run([python,str(E/'NMC_prepare_audit.py')],check=True)
a='NMC_L103';cfg(a,'NMC_COMBINED_IMPORT')
if run(a):sys.exit('Combined support import failed; no unreviewed campaign rerun')
for n,m in [(104,'NMC_Driver'),(105,'NMC_ProofDriver')]:
 a=f'NMC_L{n:03}';cfg(a,m);p=E/(a+'.json');x=json.loads(p.read_text());x['command']+=['-c','NMC_native/'+m+'.c'];x['collect']=['NMC_native/'+m+'.c'];p.write_text(json.dumps(x))
 if run(a):sys.exit('Audit driver compile failed')
for n,m in [(106,'NMC_Driver'),(107,'NMC_ProofDriver')]:
 a=f'NMC_L{n:03}';x=json.loads((E/'NMC_L104.json').read_text());x={k:v for k,v in x.items()if k not in ['deps_fingerprint','source_revision','source_tree_dirty']}
 x.update(attempt=a,kind='link',module=m,sources=['NMC_native/'+m+'.c','NMC_native/NFA_WALKER.c','NMC_native/NFA_MemoryLimit.c'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NMC_native/'+m,'NMC_native/'+m+'.c','NMC_native/NFA_WALKER.c','NMC_native/NFA_MemoryLimit.c'],collect=[],expected_time='Optimized C compilation/link of unchanged audit engine and adapted driver')
 (E/(a+'.json')).write_text(json.dumps(x))
 if run(a):sys.exit('Audit driver link failed')
for n,mode in [(108,'fixtures'),(109,'scan')]:
 a=f'NMC_L{n:03}';subprocess.run([python,str(E/'NMC_audit_config.py'),a,mode],check=True)
 if run(a):sys.exit('Fidelity/NFX gate failed')
verdicts=[]
for n in range(110,140):
 a=f'NMC_L{n:03}';mode='proof'+str(n-110);subprocess.run([python,str(E/'NMC_audit_config.py'),a,mode],check=True)
 status=run(a)
 receipt=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 if status not in [0,1]or any(marker in log.lower()for marker in ['excessive memory consumption','out of memory','timed out','timeout expired']):sys.exit('Resource-stopped raw group: isolate/split before any continuation, no cap/timeout increase')
 verdicts.append(dict(attempt=a,group=mode,exit=status))
 (E/'NMC_RAW_GROUP_STATUSES.json').write_text(json.dumps(verdicts,indent=2)+'\n')
a='NMC_L140';subprocess.run([python,str(E/'NMC_audit_config.py'),a,'close'],check=True)
sys.exit(run(a))
