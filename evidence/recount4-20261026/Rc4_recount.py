"""Ledger_003–005 atomic-family enumeration on reviewed kernel expansions.
Classification/correspondence is reviewed; enumeration/diffs/totals are mechanical.
No outer-binder count, hidden-structure discount, or logical-solver claim.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
baseline=R/'evidence/recount3-20261026/Rc3_premises.json'
before=json.loads(baseline.read_text());plan=json.loads((P/'Rc4_audit_plan.json').read_text())
logs={};evidence=[];catalog={}
for a in plan:
 receipt=json.loads((P/a['attempt']/'receipt.json').read_text())
 assert receipt['exit_status']==0,a
 log=(P/a['attempt']/'stdout.log').read_text();name=a['module'].removeprefix('Rc4_Audit');logs[name]=log
 assert not re.search(r'\berror(?:\(|:)',log),(name,'audit error')
 evidence.append(dict(attempt=a['attempt'],module=a['module'],stdout_sha256=sha(P/a['attempt']/'stdout.log')))
 for block in re.split(r'(?=^structure )',log,flags=re.M):
  if not block.startswith('structure ') or 'fields:\n' not in block:continue
  key=re.match(r'structure (\S+)',block)[1];fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
  catalog[key]=dict(audit=name,fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
for token in ['@AspisR1.Rc3_Top.deployed','@AspisR1.Rc4_Top.deployed','@AspisR1.TxS_Top.deployed','@AspisR1.SAQ_CompleteTop.deployed']:
 assert token in logs['BeforeAfter']
for token in ['Rc4_Result.Outcome','Rc2_Events.Facts','Rc2_Protection.Facts','Q0 + Q1 + 34','PerAttemptEnvelope.B','1 / 2 ^ 100']:
 assert token in logs['Statement'],token
for token in ['TxS_Encoding.Facts','Rc3_Nonvacuity.Facts','NP6_Constructors.Contents','Rc4_Caller.Outcome']:
 assert token in logs['Result'],token
for token in ['Rc4_Model.typed','TxS_Carriers.source','F3J_SamplerRun.program','SAP_FinishSaved.Outcome','Tx2N_Reader.writer']:
 assert token in logs['Literal'],token
assert 'TxS_Carriers.data' in logs['RawCarriers']
# These owners are absent as INPUTS of the new literal/continuation, and are
# derived in the checked proof. They still occur in audits of OLD interfaces.
for name in ['Literal','Continuation']:
 assert '∀ (ports :' not in logs[name]
for token in ['Port4D_Pairing.PairingLaws','MatchingSupport.match0','R3SemanticRemainingJoins.EquationEndpoint','LiteralOpeningView.eK','CheckpointBytes4ReaderFields.sourceE']:
 assert token in logs['Finish'],token
assert len(catalog['AspisR1.S2Trust.S2TrustedSdkBorrow']['field_names'])==15
assert len(catalog['AspisR1.Rc4_Model.Input']['field_names'])==5
assert len(catalog['AspisR1.TxS_Carriers.Metadata']['field_names'])==7
assert 'initFits' not in catalog['AspisR1.Rc4_Model.Input']['fields']
assert '.data :' not in catalog['AspisR1.TxS_Carriers.Metadata']['fields']
# Scope checks are on actual source, not substring deletion of printed outputs.
top=(R/'lean/Rc4_Top.lean').read_text();literal=(R/'lean/Rc4_Literal.lean').read_text().split('theorem strengthen')[0]
assert 'primitiveOwner' not in top and 'prepareOwner' not in top
assert 'Rc4_Assemble.deployed' in top
assert '(metadata : TxS_Carriers.Metadata)' in literal
assert 'let i := TxS_Carriers.source metadata' in literal
assert '(i : RecordedBinaryExperimentBin.SourceInputs)' not in literal
assert '∀ (ports :' not in literal
assert 'saved=Tx2N_Reader.writer' in literal
# The EXACT old N115 was already discharged on Rc3's source Context.
assert 'N115' not in {r['id'] for r in before['rows']}
primitive={f'N{n:03}' for n in range(47,108)}
carriers={'L151','L152','L153'};alias={'L178'}
removed=primitive|carriers|alias
byid={r['id']:r for r in before['rows']}
assert removed<=byid.keys()
assert all(byid[i]['owner']=='session A' and byid[i]['classification']=='P' for i in primitive)
assert all(byid[i]['owner']=='lead' and byid[i]['classification']=='P' for i in carriers)
# Reviewed atomic shape of SAQ's61:5 basis+9 mulE+9 addE+5 mulK+4 M31+
#1 decoder+1 line+8 line canonical+7 geometry canonical+9 domain+3 identities.
groups={'basis':range(47,52),'mulE':range(52,61),'addE':range(61,70),'mulK':range(70,75),
 'm31':range(75,79),'decoder':[79],'line':[80],'line canonical':range(81,89),
 'geometry canonical':range(89,96),'domain':range(96,105),'geometry identities':range(105,108)}
groups={k:[f'N{i:03}' for i in v] for k,v in groups.items()}
assert set().union(*(set(v) for v in groups.values()))==primitive
rows=[];diff=[]
def tag(r):
 i=r['id']
 if i in {'L094','L095','L096','L180'} or i.startswith('Rc2_P'):return 'CPH_'
 if i=='L099':return 'PFin_'
 if i in {'L157','L159','L165','L181','L182','L185'}:return 'F3X_'
 if r['owner']=='session A' and r['scope']=='actual antecedent':return 'SAF_'
 if i in {f'L{n}' for n in range(195,200)}:return 'P6B_'
 return 'UNCOVERED'
for old in before['rows']:
 r=dict(old)
 if r['id'] in removed:
  reason=('Derived on SAQ source-selected query/geometry dictionary in Rc4_Literal.strengthen and Rc4_Assemble'
    if r['id'] in primitive else
    'Derived model-instance laws via raw public carrier and decoder-produced matching Data; exact reverse transport, not native arithmetic discharge'
    if r['id'] in carriers else
    'Retire obsolete umbrella of N001–N114; all those source-selected families already derived; no independent credit')
  diff.append(dict(**r,change='removed',reason=reason));continue
 r.update(status='still present',running_job=tag(r),evidence='Rc4 fresh kernel statement/field audits028–060; retained atomic-family correspondence')
 r['owner_waits']=['implementation/association work; no new owner decision requested']
 if r['id'] in {'L157','L159','L165','L181','L182','L185'}:
  r['blocker']='Frozen3 APPROVED. This top retains the frozen2 compatibility path; integrate charged frozen3 raw/source/runtime/oracle event transport, including rejected prefixes. F3X_ coverage is planned, not imported or credited.'
 if r['id'] in {'L094','L095','L096','L180'}:
  r['blocker']='Game(a–d) and RuntimePersistence APPROVED; concrete same-bank-lineage, same-physical-CP account/actions and committed/loaded byte association still needed. CPH_ not imported or credited.'
 if r['id']=='L186':r['blocker']='Associate exact selected query/geometry/error constructor/circle/source bodies to frozen ELFs, retaining all native/extraction/runtime boundaries. Callback selection is not deployment equivalence.'
 if r['id']=='L187':r['blocker']='Focused coherent-cache composition only; final frozen dependency replay remains a release gate, excluded from this job.'
 rows.append(r);diff.append(dict(**r,change='retained',reason=r.get('blocker','Retained exact family')))
def counts(rr):
 return dict(rows=len(rr),classes={c:sum(r['classification']==c for r in rr) for c in ['T','P','C']},
  owners=dict(Counter(r['owner'] for r in rr)),by_owner={o:{c:sum(r['owner']==o and r['classification']==c for r in rr) for c in ['T','P','C']} for o in ['lead','session A','external']})
summary={s:counts([r for r in rows if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
summary['all retained audit rows']=counts(rows)
summary['deduplicated actual plus non-alias deployment']=counts([r for r in rows if r['scope']!='deployment alias'])
assert summary['actual antecedent']['classes']==dict(T=82,P=49,C=0)
assert summary['actual antecedent']['by_owner']=={'lead':dict(T=0,P=15,C=0),'session A':dict(T=0,P=31,C=0),'external':dict(T=82,P=3,C=0)}
assert summary['deduplicated actual plus non-alias deployment']['classes']==dict(T=88,P=62,C=0)
assert summary['all retained audit rows']['classes']==dict(T=88,P=65,C=0)
result=dict(actual_theorem='AspisR1.Rc4_Top.deployed',method=__doc__,baseline=str(baseline.relative_to(R)),baseline_sha256=sha(baseline),
 statement_evidence=evidence,counts=summary,actual_removals=64,session_A_removals=61,lead_removals=3,
 saq_claim_verified=sorted(primitive),txs_claim_verified=['N115','L151','L152','L153'],
 txs_incremental=sorted(carriers),already_removed_on_Rc3=['N115'],removed_alias=sorted(alias),added_actual_law_families=[],
 saq_atomic_groups=groups,rows=rows,diff=diff,
 remaining_P_by_running_job=dict(Counter(r['running_job'] for r in rows if r['classification']=='P')),
 caveat='Source-selected dictionary and actual-sampler continuation; model-instance carrier laws derived, not arbitrary native arithmetic. Frozen2 compatibility headline retained; frozen3 release target not established.')
(P/'Rc4_premises.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
(P/'Rc4_field_catalog.json').write_text(json.dumps(catalog,indent=2,ensure_ascii=False)+'\n')
text='# Remaining P families on Rc4_Top\n\nCoverage tags identify planned jobs, not imported results or closure credit. UNCOVERED includes intentionally retained success-event and external budget guards.\n\n| ID | Scope | Owner | Running job | Family | Blocker |\n|---|---|---|---|---|---|\n'
for r in rows:
 if r['classification']=='P':text+='| '+' | '.join(str(r.get(k,'')).replace('|','\\|').replace('\n',' ') for k in ['id','scope','owner','running_job','name','blocker'])+' |\n'
(P/'Rc4_REMAINING.md').write_text(text)
print(json.dumps(dict(counts=summary,actual_removals=64,retired_aliases=1,coverage=result['remaining_P_by_running_job']),indent=2))
