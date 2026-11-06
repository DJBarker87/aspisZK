"""Check successful hypothesis/owner print before completing candidate review."""
from pathlib import Path
import json,lzma,re
E=Path(__file__).resolve().parent
p=E/'NKH_audit/review-close/review.json';rc=json.loads(p.read_text());assert rc['exit_status']==0
p=E/'NKH_audit/review-close/review.log';raw=p.read_text()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes()).decode()
extra={};matchers=[]
for l in raw.splitlines():
 if 'NKH_OWNER 'in l:
  x=json.loads(l.split('NKH_OWNER ',1)[1]);assert x['root']not in extra;extra[x['root']]=x
 if 'NKH_MATCHER_OWNER 'in l:matchers.append(json.loads(l.split('NKH_MATCHER_OWNER ',1)[1]))
assert set(extra)=={'NJJ_Value.projection','NJR_WeightFailure.weights'}
assert extra['NJJ_Value.projection']['owner_module']=='NJJ_Value'
assert extra['NJR_WeightFailure.weights']['owner_module']=='NJR_WeightFailure'
assert matchers and len({x['root']for x in matchers})==len(matchers)
assert {x['owner_module']for x in matchers}=={'JFw_Validator','JFw_Record'}
axioms=rc['print_axioms'];assert len(axioms)==sum(l.startswith('#print axioms')for l in(E/'NKH_HypothesisReview.lean').read_text().splitlines())==49
assert not any('sorryAx'in l for l in axioms)
for l in axioms:
 m=re.search(r'depends on axioms: \[(.*?)\]',l)
 if m:assert set(re.sub(r'\.\{[^}]+\}', '', x.strip())for x in m[1].split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}
(E/'NKH_EXTRA_STATEMENTS.json').write_text(json.dumps(extra,indent=1)+'\n')
(E/'NKH_MATCHER_OWNERS.json').write_text(json.dumps(dict(status='PASS',unique_owners=True,roots=matchers,attempt='NKH_L040',replaced_failed_diagnostic='NKH_L039',print_axioms=axioms),indent=1)+'\n')
print(json.dumps(dict(hypothesis_owner_review='PASS',extra_roots=len(extra),matchers=len(matchers),axiom_lines=len(axioms))))
