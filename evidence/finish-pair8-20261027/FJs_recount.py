"""Retain the inherited atomic-family ledger; remove only the two checked L142 rows."""
from pathlib import Path
import json,hashlib,copy
P=Path(__file__).resolve().parent;R=P.parents[1]
base=R/'evidence/finish-pair7-20261027/FJr_recount.json'
j=json.loads(base.read_text());rows=copy.deepcopy(j['rows'])
removed={'L142','F3Y_G_L142'}
def counted(rs):return [r for r in rs if r['id']!='L166' and r['id'] not in removed]
def count(rs):return {c:sum(r['classification']==c for r in rs) for c in 'TPGC'}
def groups(rs):
 return {scope:count([r for r in rs if r['scope']==scope]) for scope in ['actual antecedent','deployment only','deployment alias']} | {'deployment-inclusive non-alias':count([r for r in rs if r['scope']!='deployment alias'])}
before=groups([r for r in rows if r['id']!='L166']);assert before==j['before'],(before,j['before'])
for row in rows:
 if row['id'] in removed:
  assert row['classification']=='P' and row['scope']=='actual antecedent'
  row.update(status='discharged in FJs_Top.deployed',running_job='FJs_',blocker=None,
   evidence='FJs_Literal.strengthen042; FJs_Result.strengthen045; FJs_GlobalPair.law047; FJs_GlobalOwners.complete048; FJs_Top.deployed; FJs_Statements kernel type audit')
after=groups(counted(rows));delta={c:after['actual antecedent'][c]-before['actual antecedent'][c] for c in 'TPGC'}
assert delta==dict(T=0,P=-2,G=0,C=0)
out=dict(actual_top_before='AspisR1.ARX_Root.deployed',actual_top_after='AspisR1.FJs_Top.deployed',
 method=j['method'],baseline=str(base.relative_to(R)),baseline_sha256=hashlib.sha256(base.read_bytes()).hexdigest(),
 inherited_adjustments=j['inherited_adjustments'],before=before,after=after,delta=delta,rows=rows,
 removed_by_this_job=sorted(removed),added_by_this_job=[],reclassified_by_this_job=[],
 premises_removed=sorted(removed),premises_added=[],job='FJs finish-pair8: native/global L142 discharge',
 source_comparison='FJs_source_comparison.json',kernel_comparison='FJs_kernel_comparison.json',
 nonvacuity='FJs_Nonvacuity.owners and FJs_Nonvacuity.conditional')
(P/'FJs_recount.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(before=before,after=after,delta=delta)))
