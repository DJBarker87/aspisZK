"""Ledger_003–005 atomic quantified-law recount for the checked Rc3 successor.
Correspondence is reviewed; row enumeration and totals are mechanical.
"""
from pathlib import Path
from collections import Counter
import hashlib,json
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
baseline=R/'evidence/recount3-20261026/Rc3_premises.json'
before=json.loads(baseline.read_text())
removed=set(f'L{n}' for n in range(110,122))|{'L125','L127','L128','L139','L140','L141','L148'}
assert len(removed)==19
rows=[];diff=[];table=[]
blockers={
'L133':'Round0: Configuration.finish.field/add remain abstract, and the actual source View.round0 coefficients are not identified with i.data.p0 by a checked installed primitive/data join.',
'L134':'Round0: finish.quarter/mulM have no installed native finite-field refinement at this dictionary; source success supplies the return, not its quarter meaning.',
'L135':'Round0: finish.polynomial remains abstract; the candidate unrolled-polynomial value theorem uses a different concrete dictionary/carrier and needs an explicit source-byte/model p0 join.',
'L136':'Round1: Configuration.finish.field/add remain abstract, and the actual source View.round1 coefficients are not identified with i.data.p1 by a checked installed primitive/data join.',
'L137':'Round1: finish.quarter/mulM have no installed native finite-field refinement at this dictionary, including the preceding actual polynomial result as claim.',
'L138':'Round1: finish.polynomial remains abstract; concrete candidate polynomial semantics are not instantiated at this exact dictionary and model p1.',
'L142':'finish.newWeights/pair are abstract. S3 grouped pair-loop invariants and S9 factor semantics need concrete source operation, coefficient-array, challenge and model dual-fold bindings at this dictionary.',
'L143':'The retained query ports supply accumulation/line meanings, not the source first-fold -> MatchingSupport.foldWord interpretation and all22 selected match0 equations. S4 indexed/tail zero-scanner equivalence is an SDK zero-byte scan, not this law.',
'L144':'The actual semantic first boundary/claim at the same literal parser/view/polynomials is not joined to the source semantic execution. Config.boundaries installs circle only, not this arithmetic endpoint.',
'L145':'Nine successive source semantic round equations are not composed with the same EquationEndpoint parsed view/polynomials and challenge sequence.',
'L146':'The terminal source call has not been identified with the exact masked spend terminal on i.decoded and i.data.Y at the same literal transcript.',
'L147':'finish.dot is abstract. S5 returned-residue/indexed-source-sum theorems apply to withConcreteDot/finishConcreteField/QRaw, requiring a concrete sourceDot installation, decoder agreement, 64 matching final-message reads and actual accumulator-weight bindings.'}
for old in before['rows']:
 r=dict(old)
 if r['id'] in removed:
  if r['id']=='L148':
   theorem='AspisR1.SAF_AcceptedValue.value'
   reason='Unnecessary on this already-accepted source run: transport physical equality forward. Canonicality itself is not claimed true for arbitrary raw values.'
  elif r['id'] in {'L139','L140','L141'}:
   theorem='AspisR1.SAF_PreparedPairing.identities'
   reason='Derived from actual saved-Vec encoding, existing reached-TX2 byte identity, installed reader BodyMatches and the SAME literal Context.'
  else:
   theorem='AspisR1.SAF_Returns.finish'
   reason='Derived by inversion of the SAME successful installed finish body; primitive operands/results are existential outputs, with no replacement Prop-law guard.'
  d=dict(**r,change='removed',theorem=theorem,reason=reason,checked_top='AspisR1.SAF_Deployed.deployed')
  diff.append(d);table.append(d)
 else:
  r['status']='retained'
  if r['id'] in blockers:r['blocker']=blockers[r['id']]
  rows.append(r);diff.append(dict(**r,change='retained'))
  if r['id'] in blockers:table.append(dict(**r,change='open',theorem='none: exact installed instance not proved'))
assert len(table)==31
assert len(diff)==len(before['rows'])
assert {r['id'] for r in table if r['change']=='open'}==set(blockers)
def counts(rs):
 return dict(rows=len(rs),classes=dict(Counter(r['classification'] for r in rs)),owners=dict(Counter(r['owner'] for r in rs)))
scopes={s:counts([r for r in rows if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
scopes['all retained audit rows']=counts(rows)
scopes['deduplicated actual plus non-alias deployment']=counts([r for r in rows if r['scope']!='deployment alias'])
assert scopes['actual antecedent']['classes']=={'T':82,'P':94}
assert scopes['actual antecedent']['owners']=={'external':85,'lead':18,'session A':73}
assert scopes['deduplicated actual plus non-alias deployment']['classes']=={'T':88,'P':107}
output=dict(actual_theorem='AspisR1.SAF_Deployed.deployed',baseline_theorem=before['actual_theorem'],baseline=str(baseline.relative_to(R)),baseline_sha256=sha(baseline),method=__doc__,removed_actual_P=19,removed_actual_T=0,added_law_families=0,counts=scopes,rows=rows,diff=diff,assigned_rows=table,quantifier_note='Primitive-return operands are actual existential outputs. SAF_CompatibleTop checks the exact original Rc3 conclusion; SAF_RoundUnique/Forget prove no loss of the old universal return continuation. Context, source/model witnesses, failure event and remaining guards are unchanged.',nonvacuity='Rc3 conditional SAME-cut Facts retained. 569 inherited source/successful exact-default-ELF evidence hashes rechecked; no claim of joint inhabitation of all residual laws or the old raw frozen2 deployment boundary.')
(P/'SAF_premises.json').write_text(json.dumps(output,indent=2)+'\n')
lines=['# Finish-law row table','','Counted successor: `AspisR1.SAF_Deployed.deployed`; baseline: `AspisR1.Rc3_Top.deployed`.','','| Row | Law | Status | Theorem or exact blocker |','|---|---|---|---|']
for r in sorted(table,key=lambda r:r['id']):
 detail=('`'+r['theorem']+'`: '+r['reason']) if r['change']=='removed' else r['blocker']
 lines.append(f"| {r['id']} | {r['name']} | {r['change']} | {detail.replace('|','/')} |")
lines+=['','Actual: **82T+113P →82T+94P**. Session A92→73; lead18/external3P unchanged.',
'Deduplicated actual plus non-alias deployment: **88T+126P →88T+107P**.',
'Assigned finish31→12: pairing7, matching1, semantic3, dot1. No T/C removal or new law family.',
'Canonicality is unnecessary in the accepted-only argument; it is not asserted as a derived source fact.',
'Full before/after statements and all nested field expansions are in the final focused audits; raw source/dependency-pinned receipts are authoritative.']
(P/'SAF_ROWS.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(scopes,indent=2))
