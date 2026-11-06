from NLM_audit import audit
from NLM_formal import E,json
import sys
jobs=[('NLM_L145','fixtures'),('NLM_L146','scan')]+[('NLM_L'+str(147+i).zfill(3),'batch'+str(i)) for i in range(len(json.loads((E/'NLM_AUDIT_ROOTS.json').read_text())['groups']))]
start=int(sys.argv[1]) if len(sys.argv)>1 else 0
for i,(a,target) in enumerate(jobs):
 if i<start:continue
 assert not (E/a).exists(),'Never resubmit an existing audit; inspect/split failures'
 r=audit(a,'audit',target)
 if r['exit_status']:sys.exit(r['exit_status'])
