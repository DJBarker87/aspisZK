#!/usr/bin/env python3
"""Review explicit law-family changes at the actual new headline.
No binder/record discount; native-local and world-global rows stay separate.
"""
from pathlib import Path
from collections import Counter
import copy,hashlib,json,re
E=Path(__file__).resolve().parent;ROOT=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bp=ROOT/'evidence/frozen3-head6-20261026/F3Y_premises.json';old=json.loads(bp.read_text())
rp=ROOT/'evidence/recount6-20261026/Rc6_premises.json';rc6=json.loads(rp.read_text())
logs={};catalog={};receipts=[]
for p in sorted(E.glob('FGl_*/receipt.json')):
 r=json.loads(p.read_text())
 if r['exit_status']:continue
 mod=r['sources'][0][:-5];s=(p.parent/'stdout.log').read_text();logs[mod]=s
 receipts.append(dict(attempt=r['attempt'],module=mod,stdout_sha256=sha(p.parent/'stdout.log')))
 for block in re.split(r'(?=^structure )',s,flags=re.M):
  if not block.startswith('structure ') or 'fields:\n' not in block:continue
  name=re.match(r'structure (\S+)',block)[1]
  fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
  catalog[name]=dict(fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
comp=logs['FGl_AuditComposition']
for name,label in [('F3Y_Headline.deployed','BEFORE'),('Rc6_Top.deployed','RC6_BEFORE'),('FGl_Headline.deployed','AFTER'),('FGl_Nonvacuity.composed','NONVACUITY')]:
 start=comp.index('@AspisR1.'+name+' :');end=comp.find('\n@AspisR1.',start+1)
 if end<0:end=len(comp)
 text=comp[start:end].split("\n'AspisR1.",1)[0]
 (E/('FGl_'+label+'.lean.txt')).write_text(text.rstrip()+'\n')
after=(E/'FGl_AFTER.lean.txt').read_text()
for x in ['FGl_PreparedAt.Owners','Rc6_Result.Outcome','P6Boundary','F3Y_SourceClaims.Claims','F3Y_AccountMass.Claims','CPH_Recorder.Facts']:
 assert x in after,x
assert 'F3Y_PreparedAt.Owners' not in after
owners=logs['FGl_AuditNewOwners'].split('def AspisR1.FGl_PreparedAt.Owners',1)[1]
assert 'FGl_FinishLeaves.Holds' in owners
finish=logs['FGl_AuditNewFinish'].split('def AspisR1.FGl_FinishLeaves.Holds',1)[1]
assert 'sourceE' not in finish
assert len(catalog['AspisR1.FGl_FinishLeaves.PairingRemaining']['field_names'])==3
assert len(catalog['AspisR1.Port4D_Pairing.RoundLaws']['field_names'])==3
# Same source/result continuation fields other than the new Rc6 package are reused.
prev=json.loads((ROOT/'evidence/frozen3-head6-20261026/F3Y_field_catalog.json').read_text())
unchanged=[]
for key in prev.keys()&catalog.keys():
 assert prev[key]['fields']==catalog[key]['fields'],('changed inherited definition',key)
 unchanged.append(key)
assert len(unchanged)>=40,len(unchanged)
removed={'F3Y_G_L148':'FGl_FinishProof.strengthen uses SAF_AcceptedValue.value on the same successful finishCall, saved state and twelve-step returned state. FGl_Aligned/Canonical/Join/Bound/Cost compose it at every arbitrary accepted H. Canonicality is unnecessary, not proved universally.',
'L099':'Inherited Rc6_Result.strengthen/Rc6_Caller.from_cut drops FirstEntry at the same source cuts; now composed in the new headline.',
**{f'L{i}':'Inherited Rc6 parser/P6 deployment theorem, composed on the same dictionary; no new credit to this job.' for i in range(195,200)}}
rows=[];diff=[]
for raw in old['rows']:
 r=copy.deepcopy(raw)
 if r['id'] in removed:
  diff.append(dict(**r,change='removed',reason=removed[r['id']]))
 else:
  r['status']='retained';r['evidence']='FGl focused kernel inventories and SAME-cut Rc6 native outcome'
  if r['id'].startswith('F3Y_G_'):
   r['definition']='lean/FGl_PreparedAt.lean#Owners; lean/FGl_FinishLeaves.lean#Holds'
   r['blocker']='SAF explicitly retains the corresponding arithmetic/matching/semantic/dot law. No source-derived theorem supplies it in the merged closure. FGl_Transport.same_domain checks world generalisation only, not arithmetic discharge.'
  rows.append(r);diff.append(dict(**r,change='retained'))
assert {x['id'] for x in diff if x['change']=='removed'}==set(removed)
def count(rs):
 c=Counter(r['classification'] for r in rs)
 return dict(rows=len(rs),classes={k:c[k] for k in ['T','P','C']})
actual=[r for r in rows if r['scope']=='actual antecedent'];dep=[r for r in rows if r['scope']=='deployment only']
counts={scope:count([r for r in rows if r['scope']==scope]) for scope in ['actual antecedent','deployment only','deployment alias']}
counts['deduplicated actual plus non-alias deployment']=count(actual+dep)
counts['actual excluding approved game domain']=count([r for r in actual if not r['id'].startswith('Rc5_G')])
assert counts['actual antecedent']['classes']==dict(T=83,P=41,C=0),counts
assert counts['deduplicated actual plus non-alias deployment']['classes']==dict(T=89,P=49,C=0),counts
# Independent reconciliation from Rc6: -3 old account/raw rows +12 global families.
rc6ids={r['id'] for r in rc6['rows']};newids={r['id'] for r in rows}
assert rc6ids-newids=={'L157','N117','N118','L182'}
assert newids-rc6ids=={'F3Y_G_L'+str(i) for i in [133,134,135,136,137,138,142,143,144,145,146,147]}
result=dict(actual_theorem='AspisR1.FGl_Headline.deployed',baseline='AspisR1.F3Y_Headline.deployed',baseline_sha256=sha(bp),
 method='Reviewed quantified-law-family ledger; original guards, carriers and shared witnesses preserved; global/local domains not silently identified.',
 before_counts=old['counts'],counts=counts,rows=rows,diff=diff,unchanged_structure_inventories=sorted(unchanged),statement_evidence=receipts,
 assigned_global_finish=dict(before=13,after=12,newly_removed=['F3Y_G_L148'],unclosed=[r['id'] for r in actual if r['id'].startswith('F3Y_G_')]),
 against_rc6=dict(before=rc6['counts'],delta_actual_P=9,delta_deduplicated_P=9,removed=['L157','N117','N118'],added_global_families=12,warning='Net increase vs Rc6; old independent account carriers and exact source-cost conclusion are replaced, as already disclosed by F3Y.'),
 newly_proved_actual_P_delta=-1,inherited_rc6_actual_P_delta=-1,inherited_rc6_deployment_P_delta=-5,
 no_T_removed=True,no_new_trust=True,joint_release_nonvacuity='Not established; new composed conditional accepted/runtime fixture and SAME-domain weakening are checked.')
(E/'FGl_premises.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'FGl_field_catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
lines=['# FGl headline law-family ledger','','Target not yet established unconditionally. Counts are obligations, not security percentages.','',
'| Scope | F3Y before T/P | FGl after T/P | Delta T/P |','|---|---:|---:|---:|',
'| Actual, including eleven approved game clauses |83/43|83/41|0/−2|',
'| Deduplicated actual plus deployment |89/56|89/49|0/−7|',
'| Actual excluding eleven approved game clauses |83/32|83/30|0/−2|','',
'New finish work removes **one** family, F3Y_G_L148. The other −1 actual and −5 deployment are inherited Rc6 parser/P6 work, now composed. No T/C family is removed.','',
'Against Rc6: **83T/32P →83T/41P**, and **89T/40P →89T/49P** (+9P). The previously disclosed F3Y raw/account replacement removes3 old families and adds12 global finish families. It is not a net reduction vs Rc6.','',
'BEFORE F3Y: 13 global finish families and the retained native/trust/game/runtime boundary imply Rc5 native/history outcomes, model extraction/spend, source cost-or-event, charged account/runtime bound and zero-query margin.','',
'AFTER FGl: 12 global finish families and the SAME boundary imply the SAME conclusions plus the stronger Rc6 native/parser/P6 package on the SAME cuts. Global canonicality is absent; forward transport uses source success already supplied by Calls. No raw field canonicality theorem is asserted.','',
'FGl_OwnerForget.weaken maps the original global owners to the weaker owners on identical evidence. FGl_Transport.same_domain checks explicit success-conditioning adds no restriction. The new non-vacuity fixture applies the actual FGl headline but remains conditional; joint inhabitation of every release premise remains open.','',
'## Requested thirteen families','','| Row | Status | Exact reason |','|---|---|---|']
for i in [133,134,135,136,137,138,142,143,144,145,146,147,148]:
 r=next(x for x in old['rows'] if x['id']=='F3Y_G_L'+str(i))
 reason=removed['F3Y_G_L148'] if i==148 else next(x['blocker'] for x in rows if x['id']==r['id'])
 lines.append('|'+r['id']+'|'+('REMOVED' if i==148 else 'OPEN: '+r['meaning'])+'|'+reason+'|')
lines+=['','## Every retained row','','| ID | Class | Scope | Name |','|---|---|---|---|']
for r in rows:lines.append('|'+r['id']+'|'+r['classification']+'|'+r['scope']+'|'+r['name']+'|')
(E/'FGl_LEDGER.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(counts=counts,unchanged_structures=len(unchanged),global_families=12),indent=2))
