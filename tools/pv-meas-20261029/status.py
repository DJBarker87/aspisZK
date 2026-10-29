"""Summarize original receipts; never launches or replays a proof."""
from pathlib import Path
import json,hashlib,subprocess,sys
E=Path('evidence/pv-meas2-20261029')
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-731*.json'))]
mechanical=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-74*.json'))]
accepted={r['target']:r for r in receipts if r.get('accepted')}
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),charged_attempts=len(receipts),budget=100,Kani=0,native=0,accepted={m:{k:r.get(k) for k in ['attempt','source_sha256','object_sha256','exit','wall','peak_rss_kbytes','swaps','axioms']} for m,r in accepted.items()},mechanical=dict(total=len(mechanical),accepted=sum(r.get('accepted',False) for r in mechanical),void=[r['attempt'] for r in mechanical if r.get('void')],failed=[r['attempt'] for r in mechanical if not r.get('accepted') and not r.get('void')]),next_target=sys.argv[1] if len(sys.argv)>1 else None)
if (E/'external-addendum-manifest.json').exists():
 a=E/'external-addendum-manifest.json';result['addendum_sha256']=hashlib.sha256(a.read_bytes()).hexdigest();result['addendum_count']=len(json.loads(a.read_text())['modules'])
result['compile_guard_sha256']=hashlib.sha256(Path('tools/pv-meas-20261029/compile.py').read_bytes()).hexdigest()
(E/'validation-progress.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(charged_attempts=len(receipts),checked=list(accepted),mechanical=result['mechanical'],next_target=result['next_target'])))
