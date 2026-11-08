from pathlib import Path
import json
E=Path(__file__).resolve().parent
receipts=[json.loads(p.read_text())for p in sorted(E.glob('NNM_L*/receipt.json'))]
proofs=[json.loads(p.read_text())for p in sorted((E/'NNM_audit').glob('batch*/proof*.json'))]
print(json.dumps(dict(completed_scopes=len(receipts),last=receipts[-1]['attempt']if receipts else None,raw_groups=len(proofs),raw_roots=sum(len(p['results'])for p in proofs),failed={r['attempt']:r['exit_status']for r in receipts if r['exit_status']},submitted=[json.loads(l)['attempt']for l in(E/'NNM_ATTEMPTS.jsonl').read_text().splitlines()if json.loads(l).get('event')=='submission'][-1:])))
