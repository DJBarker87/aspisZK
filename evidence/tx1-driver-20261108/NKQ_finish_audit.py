"""Read-only recovery after local classifier's namespace/key typo; never replay101."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
assert not(E/'NKQ_CLIENT_ACTIVE').exists(),'Wait for active scope/collection'
j=json.loads((E/'NKQ_audit/proof23/proof23.json').read_text());r=json.loads((E/'NKQ_L101/receipt.json').read_text());bad=[x for x in j['results']if not x['equal']]
assert r['exit_status']==j['exit_status']==1 and len(j['results'])==len(json.loads((E/'NKQ_AUDIT_ROOTS.json').read_text())['groups'][23])
assert len(bad)==1 and bad[0]['root']=='NHC_DecodeModel.decoder_error'and bad[0]['collect_axioms']==[] and set(bad[0]['walked_axioms'])=={'propext','Classical.choice','Quot.sound'}
for n,mode in [(78+i,'proof'+str(i))for i in range(24,31)]+[(109,'close')]:
 a=f'NKQ_L{n:03d}';assert not(E/a/'receipt.json').exists(),'Never resubmit'
 subprocess.run([sys.executable,str(E/'NKQ_audit_config.py'),a,mode],check=True)
 q=subprocess.run([sys.executable,str(E/'NKQ_run.py'),a]);assert(E/a/'receipt.json').exists(),'Recover submitted scope read-only';assert q.returncode==0,(a,q.returncode)
print('One full audit completed; original101 exit1 retained',flush=True)
