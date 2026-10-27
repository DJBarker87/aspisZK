#!/usr/bin/env python3
"""Render reviewed law-family decisions; does not prove a logical discharge."""
from pathlib import Path
import collections,copy,hashlib,json
root=Path(__file__).resolve().parents[2]
p=Path(__file__).resolve().parent
baseline=root/'evidence/tx2-resume-20261026/T2R_premises.json'
before=json.loads(baseline.read_text())
strict={f'N{i:03}' for i in range(1,47)}
source={f'N{i:03}' for i in range(108,115)}
lead={'L129','L130','L131','L132','N115'}
removed=strict|source|lead
rows=copy.deepcopy(before['rows'])
actual={r['id']:r for r in rows if r['scope']=='actual antecedent'}
assert len(removed)==58 and removed<=actual.keys()
assert all(actual[x]['owner']=='session A' and actual[x]['classification']=='P' for x in strict|source)
assert all(actual[x]['owner']=='lead' and actual[x]['classification']=='P' for x in lead)
assert 'N116' not in removed
for r in rows:
 if r['id'] in removed and r['scope']=='actual antecedent':
  r['scope']='removed by SAP at source specialization'
  r['status']='strict owner discharge' if r['id'] in strict else 'actual sampler/Context specialization and derivation'
  r['evidence']='SAP_101/stdout.log; lean/SAP_LiteralTop.lean; SAP_SourceConsumer; SAP_CloseConsumer'
  r['blocker']='none at the stated installed-source specialization; no arbitrary-transcript claim'
counts={}
for scope in ['actual antecedent','deployment only','deployment alias']:
 rr=[r for r in rows if r['scope']==scope]
 counts[scope]={'classes':dict(collections.Counter(r['classification'] for r in rr)),
                'owners':dict(collections.Counter(r['owner'] for r in rr))}
assert counts['actual antecedent']['classes']=={'T':82,'P':108}
assert counts['actual antecedent']['owners']=={'external':85,'lead':13,'session A':92}
report={'method':before['method'],'actual_theorem':'AspisR1.SAP_LiteralTop.deployed',
 'baseline':str(baseline.relative_to(root)),'baseline_sha256':hashlib.sha256(baseline.read_bytes()).hexdigest(),
 'statement_evidence_sha256':hashlib.sha256((p/'SAP_101/stdout.log').read_bytes()).hexdigest(),
 'strict_compatible_theorem':'AspisR1.SAP_Top.deployed',
 'strict_removed_rows':sorted(strict),'source_specialized_preparation_rows':sorted(source),
 'source_specialized_lead_rows':sorted(lead),'added_actual_law_families':[],
 'already_removed_not_counted':['N116','L085','L086','L087','L122','L123','L124','L126'],
 'counts':counts,'structural_rows_retained':['L151','L152','L153'],
 'scope':'circle-source installation; actual33-row sampler and actual Context. Not a universal-erasure theorem for arbitrary q/tr/data/rho/Context.',
 'rows':rows}
(p/'SAP_premises.json').write_text(json.dumps(report,indent=2)+'\n')
text='''# Recount on the actual installed-source top

Target not yet established. Baseline is T2R_Top, not the older Cons_Top.
Full before/after kernel statements and changed definitions: SAP_101/stdout.log.
The renderer applies reviewed atomic-family classification and deduplication;
it is not an automated logical discharge checker. Shared witnesses, guards and
quantified families are retained; fixed limbs split exactly as in the ledger.
No shared ledger or session A file is modified.

| Scope | T | P | lead | session A | external |
|---|---:|---:|---:|---:|---:|
| T2R baseline actual |82|166|18|145|85|
| Strict SAP_Top compatibility at installed circle |82|120|18|99|85|
| SAP_LiteralTop actual sampler/Context specialization |82|108|13|92|85|

Strict same-conclusion removal: **46 Session A families N001–N046**. The
configuration's circle field is explicitly source-installed; exact equality
with the old configuration holds iff its circle was already that source.
All other Configuration fields are proved unchanged by SAP_ConfigScope.

The source-specialized top additionally derives/consumes **7 Session A families
N108–N114** and **5 lead families L129–L132,N115**. Thus53 Session A families and58
total P families are absent as obligations at that actual source specialization.
This is NOT a58-row weakening of the unrestricted old statement: the old
arbitrary q/tr/data/rho/Context continuation is replaced with discovery and full
Prepared equality for the actual33-row sampler and its actual Context. Both
boundaries are stated explicitly; no new Prop/trust item substitutes for them.
SAP_PortUnique.no_all_rho refutes the blanket universal preparation port at a
fixed Prepared; it does not refute the full collisional security theorem.

N116 was already removed by T2R and receives ZERO new credit. The same applies
to its frozen Params and reader-observation removals. Intrinsic model carrier
families L151–L153 are conservatively retained, rather than silently crediting
existential specialization as a new source/arithmetic theorem. Deployment-only
and alias rows are unchanged. All retained audit rows:88T+127P; deduplicated
actual plus non-alias deployment:88T+122P. This is not a security percentage.

The numerical compatibility headline, adversaries, failure event, constants,
SDK/std/runtime/allocator/extraction/P1/syscall and native acceptances remain.
The old frozen2 raw join is retained only in that compatibility headline; it
is not an adopted frozen3 release claim. SAP_FrozenSdk separately consumes the
derived owner in the existing frozen3 source/model log-and-acceptance theorem,
with all its remaining primitive/five-owner leaves explicit. No independent
existential run is substituted into SAP_LiteralTop.

Non-vacuity: the final top keeps SAME-cut conditional T2R_Acceptance.Facts;
SAP_Nonvacuity projects its accepted1880-byte/tag2 input and not-all-reject
conclusion under the original history/P2Prime. SAP_NONVACUITY.json freshly
matches562 source and7 retained runtime evidence hashes for the successful
exact-default-ELF pair. Joint kernel inhabitance of every runtime/crypto/model
premise is still unproved; no fresh runtime execution is claimed.
'''
(p/'SAP_LEDGER_DELTA.md').write_text(text)
print(json.dumps({'removed_strict':len(strict),'source_session_A':len(strict|source),'source_total':len(removed),'counts':counts}))
