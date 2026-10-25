"""Reviewed law-family delta using the original Cons recount's atomic unit.
This renders audit decisions; it is not a logical discharge checker.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re
out=Path(__file__).resolve().parent
root=out.parents[1]
baseline=root/'evidence/consolidate-20261026/Cons_premises.json'
x=json.loads(baseline.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
log=(out/'T2R_080/stdout.log').read_text()
assert '@AspisR1.Cons_Top.deployed' in log and '@AspisR1.T2R_Top.deployed' in log
assert len(json.loads((out/'T2R_080/receipt.json').read_text())['print_axioms'])==20
finish=(root/'lean/T2R_Finish.lean').read_text().split('theorem strengthen')[0]
ten=(root/'lean/T2R_Ten.lean').read_text()
assert not any(f'({n} :' in finish for n in ['s2','ha0','ha1','has'])
assert 'parseReached' not in ten
assert '(p : FS2.Duplex.Params' not in (root/'lean/T2R_Top.lean').read_text()
removed={
'L085':('T2R_ParamTop/T2R_Top','Exact original frozen parameter instance; no free Params binder'),
'L086':('T2R_ParamTop/T2R_Top','Exact bounded original encoder instance'),
'L087':('T2R_ParamTop/T2R_Top','Exact original decoder/encoder inverse'),
'L122':('T2R_Reader.observations','SAME accepted installed op18 returns S2'),
'L123':('T2R_Reader.observations','SAME op18 alpha0 physical read, returned as output'),
'L124':('T2R_Reader.observations','SAME op18 alpha1 physical read, returned as output'),
'L126':('T2R_Reader.observations','SAME op18 two-element alpha slice, returned as output'),
'N116':('T2R_Pair.accepted/T2R_Ten','Source-selected parser already identifies proof bytes; direct Tx1Q_Model.ten retains every tr'),
}
rows=[]
for original in x['rows']:
 r=dict(original)
 if r['id'] in removed:
  assert r['scope']=='actual antecedent' and r['classification']=='P'
  r['original_scope']=r['scope'];r['scope']='removed by T2R';r['status']='discharged'
  r['discharge_theorem'],r['audit_reason']=removed[r['id']]
  r['evidence']='T2R_080/stdout.log; T2R_071/sources/T2R_Top.lean'
 elif r['scope']=='actual antecedent':
  r['status']='retained in actual T2R top'
  if r['id'] in ['L151','L152']:
   r['audit_reason']='Original universally quantified model LinearMap carrier unchanged. T2R_ModelInstances proves instance laws; no global row-removal credit.'
  if r['id']=='L153':
   r['audit_reason']='Derived at SAME accepted Input and any SAME-public-byte transcript, but arbitrary ten/finish tr still has original Public.initFits field; association remains.'
 rows.append(r)
assert set(removed)=={r['id'] for r in rows if r['scope']=='removed by T2R'}
counts={}
for scope in ['actual antecedent','deployment only','deployment alias']:
 rr=[r for r in rows if r['scope']==scope]
 counts[scope]={'classes':dict(Counter(r['classification'] for r in rr)), 'owners':dict(Counter(r['owner'] for r in rr))}
assert counts['actual antecedent']['classes']=={'T':82,'P':166}
assert counts['actual antecedent']['owners']=={'external':85,'lead':18,'session A':145}
result={'method':x['method'],'actual_theorem':'AspisR1.T2R_Top.deployed','baseline':str(baseline.relative_to(root)), 'baseline_sha256':sha(baseline),'statement_evidence_sha256':sha(out/'T2R_080/stdout.log'),'counts':counts,'removed_actual_rows':list(removed),'added_actual_rows':[],'structural_rows_retained':['L151','L152','L153'],'rows':rows}
(out/'T2R_premises.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
text='''# Actual-top recount delta

Target not yet established. Baseline: Cons_Top recount in PREMISE-LEDGER-20261025.
Method: full kernel before/after statements plus all changed factored conclusions,
structure-field baseline, split conjunctive leaves, retain quantified families,
shared witnesses/guards, reviewed classification and deduplication. This script
renders those decisions; it does not prove implications. See T2R_080/stdout.log,
T2R_LegacyResult.forget and T2R_premises.json. No shared ledger file edited.

| Actual antecedents | T | P | lead | session A | external |
|---|---:|---:|---:|---:|---:|
| Cons_Top |82|174|26|145|85|
| T2R_Top |82|166|18|145|85|
| Delta |0|-8|-8|0|0|

| Removed row | Checked source/theorem | Reason |
|---|---|---|
'''
for i,(th,reason) in removed.items():text+=f'| {i} | {th} | {reason} |\n'
text+='''
Added actual law families: **zero**. Deployment-only and alias scopes unchanged.
All retained audit rows:88T+185P; deduplicated actual plus non-alias deployment:
88T+180P. Counts describe obligations, not a security percentage.

## Requested structural rows: no global removal credit

L151/L152 remain fields of the ORIGINAL universally quantified SourceInputs/Data
LinearMaps. Par_Parameters and T2R_ModelInstances supply their unchanged instance
laws without another law premise. Those facts establish no native arithmetic.
Because the actual finish continuation still quantifies that model input, the
strict Cons law-family recount retains both structural carrier rows. Renaming
or repackaging i would not discharge them.

L153 is derived at the public Input constructed from SAME f.pub/f.proof and on
any transcript with the original same-public-byte equation. The actual ten and
finish tr quantifiers are unchanged and do not establish that association.
Their original LiteralTranscript.Public.initFits carrier field therefore remains.
T2R_CarrierGap.arbitrary_public exhibits an empty-public carrier (tag2) to rule
out a universal carrier-only1880-byte inference; this is NOT a counterexample
to joint inhabitance or the full guarded security theorem. Par's scoped accepted
Input discharge is valid; subtracting it from the actual arbitrary-tr row is not.
The requested six-row Par absorption is consequently PARTIAL: L085-L087 removed,
L151-L153 retained under this strict actual-top method. No desired conclusion
is hidden inside a new structure, callback or typeclass.

## Quantifiers, preservation and non-vacuity

Free M,Cv,N,p specialise to the unchanged SelectedTranscriptParams.params.
Native inputs/dictionaries/errors/cuts/source calls/heap/account observations,
query budgets/source experiment/project/failure event and metric are unchanged.
Finish alpha0/alpha1/alphas are existential source-selected outputs; all other
primitive and model laws stay universal at those operands. T2R_Legacy.finish
uses read determinism to recover the complete original universal continuation.
T2R_LegacyResult.forget recovers the entire original Cons_Result on the SAME
witness tuple. N116 is removed for EVERY tr, without an Aligned substitute or
an honest-only restriction. L099 entry.parsed remains, explicitly distinct.

T2R_Parser.on_run derives source prefix and stored-proof parser on SAME run;
T2R_Selected.identify proves every selected parser output (including the existing
continuation authParsed) equals that source prefix by deterministic parsing.
T2R_Acceptance.Facts in the actual top constructs an accepted same-byte Input
and excludes reject-everything under ORIGINAL protected history/P2Prime.
Native success remains a hypothesis. No unconditional runtime/model joint
inhabitance, rejected-oracle-prefix transport or source-to-ELF closure is claimed.
'''
(out/'T2R_LEDGER_DELTA.md').write_text(text)
print(json.dumps({'counts':counts,'removed':list(removed),'added':[]},indent=2))
