"""Reviewed atomic-family correspondence; mechanical enumeration, not a logical
implication checker. Ledger_003–005 quantifiers, witnesses and guards retained.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re
P=Path(__file__).resolve().parent
ROOT=P.parents[1]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
baseline=ROOT/'evidence/recount2-20261026/Rc2_premises.json'
before=json.loads(baseline.read_text())
plan=json.loads((P/'Rc3_audit_plan.json').read_text())
logs={}
for a in plan:
 if a['status'] != 'compiled': continue
 receipt=json.loads((P/a['attempt']/'receipt.json').read_text())
 assert receipt['exit_status']==0,(a['attempt'],receipt['exit_status'])
 logs[a['module'].removeprefix('Rc3_Audit')]=(P/a['attempt']/'stdout.log').read_text()
# Host launches stopped before attempt21 by the binding reservation rule.
# Reuse complete successful inherited field expansions only after validation
# pins every inherited source and the selected cached objects byte-for-byte.
saplog=(ROOT/'evidence/sessa-prepare-20261026/SAP_101/stdout.log').read_text()
rc2log=(ROOT/'evidence/recount2-20261026/Rc2_022/stdout.log').read_text()
logs['GeoGuards']=saplog
logs['Dot']=saplog+'\n'+(ROOT/'lean/SAP_FinishSaved.lean').read_text()
logs['InheritedStructures']=saplog+'\n'+rc2log
assert '@AspisR1.Rc3_Top.deployed' in logs['BeforeAfter']
assert '@AspisR1.Rc3_CompatibleTop.deployed' in logs['BeforeAfter']
assert '∃ f s, ⋯' not in logs['BeforeAfter']
catalog={}
for kind,log in logs.items():
 for block in re.split(r'(?=^structure )',log,flags=re.M):
  if not block.startswith('structure ') or 'fields:\n' not in block:continue
  name=re.match(r'structure (\S+)',block)[1]
  fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
  catalog[name]=dict(audit=kind,fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
assert len(catalog['AspisR1.S2Trust.S2TrustedSdkBorrow']['field_names'])==15
assert len(catalog['AspisR1.DrvC_Installation.Configuration']['field_names'])==9
assert len(catalog['AspisR1.SAP_LiteralFields.Fields']['field_names'])==11
(P/'Rc3_field_catalog.json').write_text(json.dumps(catalog,indent=2,ensure_ascii=False)+'\n')
# Verify the actual output, not merely named theorem presence. All tokens below
# occur in complete kernel-expanded definitions printed by independent audits.
for token in ['SAP_CurrentNumeric.numeric','LiteralMatchingData.read','LiteralOpeningView.read',
              'SAP_LiteralFields.Fields','F3J_SamplerRun.program','currentPrepared',
              'Port5Q1_QueryPorts.SessionAPrepare','Port5Q2_Prepared.PreparedFields',
              'SAP_FinishSaved.Outcome','Tx2N_Reader.writer']:
 assert token in logs['GeoGuards'],token
for token in ['pairing_S3_S5_S9','matches_S4_S7','semantic_S3_S9','dot_S5','canonical_S3_S4_S5_S9','RoundValues']:
 assert token in logs['Dot'],token
# prepare_S1 / savedVec application guards were actually consumed; these
# identifiers remain elsewhere as outputs, never erased by text subtraction.
assert 'prepare_S1' not in (ROOT/'lean/SAP_FinishSaved.lean').read_text().split('theorem consume')[0]
source=(ROOT/'lean/Rc3_Top.lean').read_text()
assert 'prepareOwner' not in source
assert 'SAP_LiteralTop.deployed' in source and 'Rc2_Base.strengthen' in source
assert 'NP6_Constructors.on_run' in source and 'Rc3_Nonvacuity.derive' in source
assert 'Rc2_Top.deployed' in (ROOT/'lean/Rc3_CompatibleTop.lean').read_text()
strict={f'N{i:03}' for i in range(1,47)}
source_a={f'N{i:03}' for i in range(108,115)}
source_lead={'L129','L130','L131','L132','N115'}
# L168 is a deployment ALIAS of precisely the removed prepare/data/saved
# families. Retiring it gives no second deduplicated premise-removal credit.
alias={'L168'}
removed=strict|source_a|source_lead|alias
rows=[];diff=[]
for old in before['rows']:
 r=dict(old)
 if r['id'] in removed:
  reason=('Derived universal immutable PreparedFields at source-installed configuration'
    if r['id'] in strict else
    'Derived actual-sampler preparation/query/data/Context and saved-Vec association; arbitrary continuation specialization explicit'
    if r['id'] in source_a|source_lead else
    'Obsolete alias of N108–N114 and N115 at the actual-source specialization; not a second independent discharge')
  diff.append(dict(**r,change='removed',reason=reason,checked_result='Rc3_CompatibleTop.deployed' if r['id'] in strict else 'Rc3_Top.deployed; SAP_LiteralOutcome'))
  continue
 r.update(status='still present',evidence='Rc3 focused kernel audits; exact inherited atomic-family correspondence')
 if r['id'] in {'L094','L095','L096','L180'}:
  r['blocker']='Owner game fields (a-d) and RuntimePersistence are APPROVED. This top still needs concrete physical same-lineage/account/action and committed/loaded bytes association; concurrent TxS_/CPH_ work is not imported.'
 if r['id'] in {'L157','L181','L182'}:
  r['blocker']='Frozen3 is APPROVED as headline target. The selected top retains the inherited frozen2 compatibility boundary; compose charged frozen3 source/raw join and numerical headline, including rejected prefixes and event transport. Concurrent F3W_ work is not imported.'
 if r['id']=='L165':r['blocker']='SAP derives actual source sampler/parser/data association (L129–L132); complete global source/model oracle event transport and raw charged join remain.'
 r['owner_waits']=['implementation/association work; no new owner decision requested']
 rows.append(r);diff.append(dict(**r,change='retained',reason=r.get('blocker',r.get('meaning','Retained exact family'))))
assert len(diff)==len(before['rows'])
actual=[r for r in rows if r['scope']=='actual antecedent']
a_by_id={r['id']:r for r in actual}
finish={
 'pairing_S3_S5_S9':list(range(133,143)),
 'r0 RoundValues':list(range(110,116)),
 'r1 RoundValues':list(range(116,122)),
 'semantic_S3_S9':list(range(144,147)),
 'matches_S4_S7':[143], 'dot_S5':[147], 'canonical_S3_S4_S5_S9':[148],
 'hw/hp/hd return equations':[125,127,128]}
binding={'primitiveOwner':list(range(47,89)),'geoLeaves':list(range(89,96)),
         'domain':list(range(96,105)),'geometry':list(range(105,108)),'prepare_S1':[]}
groups={}
for name,ids in finish.items():groups[name]=['L'+str(i).zfill(3) for i in ids]
for name,ids in binding.items():groups[name]=['N'+str(i).zfill(3) for i in ids]
session={r['id'] for r in actual if r['owner']=='session A' and r['classification']=='P'}
assert set().union(*(set(x) for x in groups.values()))==session
assert sum(map(len,groups.values()))==len(session)==92
for name,ids in groups.items():
 for i in ids:
  assert i in a_by_id and a_by_id[i]['owner']=='session A'
def counts(rr):
 return dict(rows=len(rr),classes=dict(Counter(r['classification'] for r in rr)),owners=dict(Counter(r['owner'] for r in rr)),by_owner={o:dict(Counter(r['classification'] for r in rr if r['owner']==o)) for o in ['lead','session A','external']})
summary={s:counts([r for r in rows if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
summary['all retained audit rows']=counts(rows)
summary['deduplicated actual plus non-alias deployment']=counts([r for r in rows if r['scope']!='deployment alias'])
assert summary['actual antecedent']['classes']=={'T':82,'P':113}
assert summary['actual antecedent']['owners']=={'external':85,'lead':18,'session A':92}
assert summary['deduplicated actual plus non-alias deployment']['classes']=={'T':88,'P':126}
result=dict(actual_theorem='AspisR1.Rc3_Top.deployed',method=__doc__,baseline=str(baseline.relative_to(ROOT)),baseline_sha256=sha(baseline),
 statement_evidence=[dict(attempt=a['attempt'],sha256=sha(P/a['attempt']/'stdout.log')) for a in plan if a['status']=='compiled'],
 reused_statement_evidence=[dict(path=str(f.relative_to(ROOT)),sha256=sha(f)) for f in [ROOT/'evidence/sessa-prepare-20261026/SAP_101/stdout.log',ROOT/'evidence/recount2-20261026/Rc2_022/stdout.log']],
 strict_removed=sorted(strict),source_specialized_session_A=sorted(source_a),source_specialized_lead=sorted(source_lead),removed_alias=sorted(alias),
 actual_removals=58,session_A_removals=53,strict_session_A_removals=46,added_actual_law_families=[],counts=summary,
 structural_carrier_rows_conservatively_retained=['L151','L152','L153'],rows=rows,diff=diff,
 remaining_session_A_groups={k:dict(count=len(v),ids=v) for k,v in groups.items()},
 caveat='Source-installed actual33-row sampler/Context specialization, not 58-row weakening of the unrestricted continuation; no security percentage')
(P/'Rc3_premises.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
# All remaining P rows, including deployment inventory and aliases.
text='# Remaining P families on Rc3_Top\n\nEach quantified law stays one family; shared existential witnesses/guards stay shared. Deployment aliases are not independent gates.\n\n| ID | Scope | Owner | Family | Blocker |\n|---|---|---|---|---|\n'
for r in rows:
 if r['classification']=='P':text+='| '+' | '.join(str(r.get(k,'' )).replace('|','\\|').replace('\n',' ') for k in ['id','scope','owner','name','blocker'])+' |\n'
(P/'Rc3_REMAINING.md').write_text(text)
print(json.dumps({'counts':summary,'groups':{k:len(v) for k,v in groups.items()}},indent=2))
text='''# Rc3 mechanical recount

Target not yet established. Counted theorem: `AspisR1.Rc3_Top.deployed`.
This applies Ledger_003–005's atomic quantified-law method, rather than counting
outer binders. Shared cuts/run/parsed values, same existential successors,
conditional guards and common dictionaries are preserved and deduplicated.
Classification and row correspondence are reviewed judgments; enumeration,
field extraction, row diff and totals are mechanical, not a logical solver.

Fresh kernel evidence: Rc3_009 before/after/full Result; Rc3_010–020 SDK/std/
allocator/extraction/entry/hash/child/cut/history/other-cone/RoundValues fields.
Changed literal/finish/remaining nested field expansions reuse SAP_101 and
Rc2_022, whose source/object pins were independently checked. No unrun audit
receives credit. Exact source binders are in the committed module snapshots;
they retain names even where pretty printing uses implications. 677 inherited
source hashes and98 inherited objects are unchanged; no full package replay.

| Scope | T | P | C | lead | session A | external |
|---|---:|---:|---:|---:|---:|---:|
'''
for scope,v in summary.items():
 text+='| '+scope+' | '+' | '.join(str(v['classes'].get(k,0)) for k in ['T','P','C'])+' | '+' | '.join(str(v['owners'].get(k,0)) for k in ['lead','session A','external'])+' |\n'
text+='\n| Scope / owner | T | P | C |\n|---|---:|---:|---:|\n'
for scope,v in summary.items():
 for o,cs in v['by_owner'].items():text+='| '+scope+' / '+o+' | '+' | '.join(str(cs.get(k,0)) for k in ['T','P','C'])+' |\n'
text+='''
Before Rc2: actual82T+171P; strict compatible after:82T+125P;
actual-source after:82T+113P. The inherited security slice excludes the five
Rc2 bank-protection guards:82T+166P →82T+108P. Those five guards are retained,
not newly added by Rc3. Actual P ownership: lead23→18, sessionA145→92,
external3→3. T remains82 external. No new trust/Prop-law family substitutes
for removed rows. No C discharge or percentage claim.

SAP's46 strict Session A claim checks: N001–N046 are supplied by the installed
prepare owner; Rc3_CompatibleTop keeps the exact Rc2 conclusion. Its53 claim
also checks AT THE ACTUAL SAMPLER specialization: N108–N114 add7 Session A
rows, and L129–L132/N115 remove5 lead rows, total58 actual P families. This
is not a58-row weakening of the old universal arbitrary-q/tr/data/rho/Context
continuation. Frozen params/read-observation/parser/Claims removals already
in Rc2 get zero new credit. L151–L153 intrinsic model-carrier laws remain
conservatively inventoried; existential specialization is no arbitrary source
arithmetic theorem.

Reporting correction to SAP's "deployment/aliases unchanged": L168 is an
obsolete alias of the now-derived actual prepare/data/Context/saved-Vec
families. Rc3 retires that alias too, without increasing the58 independent
actual-family delta or changing deduplicated totals. L165 remains PARTIAL:
local source sampler/parser/data join is derived, global raw/event transport
remains. Row-by-row diff for EVERY Rc2 retained row: Rc3_premises.json.diff;
remaining P owner/scope/blocker table: Rc3_REMAINING.md.

| Remaining actual Session A family | Count | IDs |
|---|---:|---|
'''
for name,ids in groups.items():text+='| '+name+' | '+str(len(ids))+' | '+(', '.join(ids) if ids else 'none')+' |\n'
text+='''
The requested finish families sum28 (pairing10, rounds12, semantic3, matching1,
dot1, canonical1); hw/hp/hd are3 further primitive return equations. Binding
families sum61 (primitiveOwner42, geoLeaves7, domain9, geometry3, prepare_S1=0).
Thus28+3+61=92 actual Session A families. The non-alias S6 deployment rowL176
is separate; L178 is the remaining Session A umbrella alias, not an extra
independent primitive gate. Original family owners stay session A even where
individual source cones are S3/S4/S5/S7/S9; this job does not reassign them.
'''
(P/'Rc3_LEDGER.md').write_text(text)
marker='\n## Recount on Rc3_Top (2026-10-26)\n'
doc=ROOT/'design/PREMISE-LEDGER-20261025.md'
prefix=doc.read_bytes().split(marker.encode())[0]
prefixhash=hashlib.sha256(prefix).hexdigest()
pin=P/'Rc3_ledger_prefix.json'
if pin.exists():assert json.loads(pin.read_text())['sha256']==prefixhash
else:pin.write_text(json.dumps(dict(bytes=len(prefix),sha256=prefixhash),indent=2)+'\n')
doc.write_bytes(prefix+marker.encode()+('\n'+text.split('\n',1)[1]).encode())
