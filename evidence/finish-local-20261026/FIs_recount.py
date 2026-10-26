from pathlib import Path
import copy,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
p=R/'evidence/recount9-20261026/Rc9_premises.json';b=json.loads(p.read_text())
removed={f'L{x}' for x in [133,134,135,136,137,138,147]}
rows=[copy.deepcopy(r) for r in b['rows'] if r['id'] not in removed]
assert {r['id'] for r in b['rows']} - {r['id'] for r in rows}==removed
root=json.loads((E/'FIs_042/receipt.json').read_text()); assert root['exit_status']==0
for r in rows:
 if r['id'] in ['L142','L143','L144','L145','L146']:
  r['definition']='lean/FIs_Finish.lean#Outcome; lean/FIs_Pair.lean#Law'
  r['evidence']='FIs_042 deployed root; FIs_036 native literal transport; fresh FIs atomic inventories'

assert all(r['classification']=='P' and r['scope']=='actual antecedent' for r in b['rows'] if r['id'] in removed)
def counts(rs):
 return {s:{c:sum(r['classification']==c for r in rs if (r['scope']==s if s!='combined' else r['scope']!='deployment alias')) for c in ['T','P','G','C']} for s in ['actual antecedent','deployment only','deployment alias','combined']}
raw=counts(rows); distinct=counts([r for r in rows if r['id']!='L137'])
assert raw['actual antecedent']==dict(T=83,P=12,G=13,C=0)
assert distinct['actual antecedent']==dict(T=83,P=12,G=13,C=0)
assert distinct['combined']==dict(T=89,P=16,G=13,C=0)
out=dict(actual_theorem='AspisR1.FIs_Top.deployed',baseline='AspisR1.Rc9_Top.deployed',baseline_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),method=b['method'],rows=rows,removed=sorted(removed),added=[],raw_counts=raw,counts=distinct,raw_delta=dict(T=0,P=-7,G=0,C=0),distinct_delta=dict(T=0,P=-6,G=0,C=0),aliases={'L185':'L159'},native_removals=sorted(removed),global_removals=[],root_receipt='FIs_042/receipt.json',statement_check='FIs_statement-check.json',nonvacuity='FIs_Nonvacuity.composed, conditional on retained assumptions and snapshots; JFs joint fixture remains OPEN')
(E/'FIs_recount.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['removed','raw_counts','counts','raw_delta','distinct_delta']},indent=2))
