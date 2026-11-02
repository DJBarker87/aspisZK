from audit10 import *
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
rows=json.loads((B/'recount9/rows9.json').read_text()); by={r['id']:r for r in rows}
def record(k,path):
 s=txt(k,path);assert s is not None,(k,path);return s
# Capture current consumers and the actual semantic definitions behind the headline.
for k,paths in {
'rw':['lean/PV_MEAS_Deployed.lean','lean/PV_MEAS_Legacy.lean','lean/PV_MEAS_Core.lean','lean/PV_EVH_Core.lean','lean/PV_EVH_Interface.lean','lean/PV_EVH_Deployed.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB3_Op225Source.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6TransitionSource.lean'],
'runjoin':['docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_NativeQueryDischarge66.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_NativeFinishDischarge69.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_NativeOriginalPublication60.lean','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_NativeResidual63.lean'],
'b3p6':['evidence/pv-b3p6-20261028/lean/PV_B3P_BridgeResidual557227.lean','evidence/pv-b3p6-20261028/lean/PV_B3P_LocalClosure557227.lean','evidence/pv-b3p6-20261028/resume18/HANDOFF.md','evidence/pv-b3p6-20261028/resume18/EXACT-BRIDGE-STATEMENT-D557.json'],
'rdcd5':['evidence/pv-rdcd5-20261101/V197-FINDING.md'],
'research':['design/PV-OWNER-PACKET-20261027.md','docs/research/v8-r0-zk-20261009/LOG.md']}.items():
 for p in paths:record(k,p)
# The only V242 whole-row lowering-only certificate predates current live heads.
pins['historical_reused_revisions']=json.loads((B/'recount9/pins.json').read_text())['revisions']
revs['fscan']=pins['historical_reused_revisions']['fscan']
record('fscan','evidence/pv-fscan-20261028/CLASSIFY.md')
for r in rows:
 r['recount9_bucket']=r['dependency_bucket'];r['recount10_status']=r['recount9_status'];r['recount10_class']=r['recount9_class']
 r['recount10_basis']='Unchanged defining bytes: retain the exact scoped derivation in recount9, subject to the current overlays below. '+r['recount9_basis']
 r['definition_witnesses10']='definition-audit10.json#'+r['id'];r['recount10_evidence']=['../recount9/rows9.json#'+r['id'],r['definition_witnesses10']]
 r['residual10']=r['residual9'];r['tool_trust10']=r['tool_trust9'];r['native_disposition10']=r['native_disposition9']
 r['axiom_audit10']='Historical #print axioms outputs are SUMMARY-BASED. No new NEP run or coherent release audit is claimed; D565 joint NDR authority is excluded.'
common='Qualified source/Result boundary only. E1/E2, actual RunJoin/native carrier/world, runtime/allocator adequacy, V370 compiler cohort, proof-account client, L1/L2/L3 and coherent release replay remain. Tool-semantic transfer is RECLASSIFICATION, not endpoint premise removal.'
def update(id,s,status=None,bucket=None,th=None,route=None,ev=()):
 r=by[id];r['recount10_basis']=s;r['recount10_evidence']+=list(ev)
 if status:r['recount10_status']=status
 if bucket:r['dependency_bucket']=bucket
 if th:r['closure_theorem']=th
 if route:r['closure_route']=route
restores={
'V201':('R1Z.PV_RDCD4_V201.source_reference','structural (K-1 substitute)','Every original generic CodeField, q1024 and Point; complete Result equality with the original owned encoder. All145 records dispositioned,11 deployed bindings; no b3p6-1 claim. Native producer and physical observations remain separate.'),
'V220':('R1Z.PV_RDCD4_V220.source_reference','structural (K-1 substitute)','Every original Array<QM31,28> and challenge; full lazy radix-four Result equality to the complete loop-free owned reference, without new callback/success premise. Original checker remains unrecovered; source bindings, not a substitute checker, support restoration. No new polynomial-meaning/canonical-reachability claim.'),
'V237':('R1Z.PV_RDCD4_V237.complete','structural plus exhaustive over a singleton input domain, deployed-configuration harness','Original generic Core::default full Result, including failure/divergence. ONLY GenericArray<u8,U64>::default is singleton: fixed64 zeros/position0,45-node influence census, address and allocator-write channels checked. Core remains the original Result parameter, not an input-free claim.'),
'V242':('R1Z.PV_CB3_Op225Source.op225_source','extraction, lowering-only compiler cohort under V370','All Public variants, arbitrary payload adapters and complete Result equation. fscan whole-row class A identifies four byte-identical pure project bodies; D502 explicitly adopts lowering-only credit under V370. This resolves the sole prior owner suspension, not compiler preservation itself.')}
for id,(th,route,s) in restores.items():
 update(id,'CONFIRM RESTORATION. '+s+' '+common,status='CLOSED-ON-CANDIDATE',th=th,route=route,ev=['independent-audit10.json#'+id])
 by[id]['native_disposition10']='RESTORED at qualified source boundary';by[id]['residual10']=common
update('V197','OPEN. rdcd5 kernel-confirmed empty-input mismatch: existing success parser returns fail.panic, owned qm returns fail.arrayOutOfBounds. Whole-Result identification is false. Local windows/geometry laws do not repair it. No deployed privacy counterexample. The old escaping-reference obstruction remains historical, but is superseded as the immediate blocker by this checked equality failure.',bucket='a',ev=['rdcd5:evidence/pv-rdcd5-20261101/V197-FINDING.md'])
update('V233','OPEN b/SUSPENDED. rdcd5 typed inverse passes78214, but exact typed roundtrip/consumed association and coherent dependent closure remain incomplete at the live pin. C002 stays SUSPENDED; C088/C089 fresh split credits have their original stubbed scope and do not supply the missing typed bridge.',ev=['rdcd5:evidence/pv-rdcd5-20261101/REPORT.md'])
update('V236','OPEN b/SUSPENDED. Complete BlockBuffer.digest_blocks branch/cursor/ordered-callback and exact typed UpdateSplit remain unbound at live rdcd5. Copy/window/geometry facts and historical finite pairs are retained, not whole-row restoration.',ev=['rdcd5:evidence/pv-rdcd5-20261101/REPORT.md'])
for id,s,bucket in [
('V373','OPEN. D502 adopts the recipe and paired throttled timing; D537 changes the shipped bundle to da36d6aa. The earlier fa888460 disassembly audit had seven unresolved kernels/345 incomplete origins and must be redone on the adopted binary. User-client candidate has a different unadopted hash. No whole compiled-kernel coverage.', 'a'),
('V374','OPEN. D502 settles timing-policy/recipe decisions, but paired throughput timing is not dudect or a whole-client leakage test. Required actual-binary setup/statistical evidence remains; decoder instruction-trace evidence has finite scope.', 'a'),
('V396','OPEN. D524 settles user-client scope; D537 adopts combined bundle da36d6aa pending user client. D561 user candidate9310ca5e has1000/1000 differential pairs and31/31 checksum checks, but zero accepted timing pairs, missing faithful25-type/119-op external bindings and decoder I32/U32 shift failure. Emission is not full-entry compilation or adoption. Native caller/upload/observer integration remains.', 'b')]:update(id,s,bucket=bucket,ev=['independent-audit10.json#client'])
for id in ['V045','V046','V047','V038','V163','V165','V167','V268','V269','V270','V397','V398','V399']:
 by[id]['recount10_basis']+=' CURRENT D502/D540/D565: Result-only endpoint is historical. Adopted event-retaining measured headline keeps Signal x Observation and simE, exact bound and three-field T. Native source/joint D163/D166/V400 links remain. NDR/90000 does NOT establish coherent non-vacuity; match_3 is undeclared in the loaded cohort. NEP hard-error result supersedes the successful import/summary outputs; no joint closure credit.'
for id in ['V241','V244','V245']:
 update(id,'OPEN/PARTIAL. V244 has36/36 local associations (4 direct extraction,2 Kani,30 Lean/structural); they compose jointly but selected_callback_residual557 still requires DeployedWrapper557 base ops. Complete formatting unreachability,16 opaque helper instances, pointer/drop/initializer/caller associations remain. Exact original runjoin callback conclusion is conditional, not closure. K-3 C155/C157 are controlled RESTORED only at bounded scope; k-double/triple-prime std transfer and V370 remain. No full catalogue, actual dictionary witness or non-emptiness inferred.',ev=['b3p6:evidence/pv-b3p6-20261028/lean/PV_B3P_BridgeResidual557227.lean'])
for id in ['V225','V400']:
 by[id]['recount10_basis']+=' CURRENT: adopted bundle uses getrandom linux_raw, removing historical dlsym interposition at this client configuration. Native acquisition/backend/errno/partial-fill/zeroize event binding and witness-independent failure are still obligations; no extra entropy or OS-availability T field.'
for id in ['V183','V228','V263']:
 by[id]['recount10_basis']+=' CURRENT runjoin installed qualified op32 world family and op132 packet; op257 is still an unbound residual. Even exact op227 cannot imply Nonempty P when op257 diverges (D564 interface counterexample). v263 branch absent at snapshot; no later work credited. Skeleton consistency: reduced to non-emptiness.'
# Scope-specific K-3 dependency check, with suspended historical observations preserved.
credits=json.loads(lzma.decompress(read('k3scan','evidence/pv-k3scan-20261101/CREDITS.json.xz')))
cb={c['credit_id']:c for c in credits}; roll=json.loads(read('k3scan','evidence/pv-k3scan-20261101/K3-ROWS.json'))['rows']
kcounts=dict(collections.Counter(c['final_status'] for c in credits));assert kcounts=={'SUSPENDED':199,'UNAFFECTED':81,'RESTORED':22,'WITHDRAWN':3}
for q in roll:
 assert not q['depends_on_still_suspended_credit'] and not q['suspended_current_support']
 for c in q['current_kani_support']:
  assert cb[c]['final_status'] in ['RESTORED','UNAFFECTED'],(q['ledger_row'],c)
 if q['ledger_row'] in by:
  by[q['ledger_row']]['k3_current_scope10']=q
  by[q['ledger_row']]['recount10_basis']+=' K-3 current support: '+q['current_credited_scope']+' '+q.get('reason','')+' Historical suspended observations remain excluded; see k3-audit10.json.'
# Machine check full current rollup support and every controlled re-run's actual receipts.
pairs=[]
for c in credits:
 if c.get('fresh_pair'):
  f=c['fresh_pair'];pos=f['positive'];neg=f['control']
  a=json.loads(read('k3scan','evidence/pv-k3scan-20261101/host/'+pos+'/receipt.json'))
  z=json.loads(read('k3scan','evidence/pv-k3scan-20261101/host/'+neg+'/receipt.json'))
  assert a['exit_status']==0 and z['exit_status']!=0 and z['negative_control']
  harness=lambda x: x['command'][x['command'].index('--harness')+1]
  assert harness(z) in [harness(a),harness(a)+'_wrong']
  for item in [a,z]:
   assert item['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64}
  pairs.append({'credit':c['credit_id'],'positive':pos,'control':neg,'positive_exit':a['exit_status'],'control_exit':z['exit_status'],'final_status':c['final_status'],'harness':harness(a),'control_harness':harness(z),'deployed_transfer':c.get('deployed_transfer'),'fresh_pair':f})
(P/'k3-audit10.json').write_text(json.dumps({'counts':kcounts,'rows':roll,'pairs':pairs,'no_current_support_suspended':True,'limits':'K-3 scope only; K-1/K-2/std/native/compiler/world restrictions retained. Negative diagnostics and unresolved sources never credited.'},indent=1)+'\n')
# Same consumer roots as recount9, plus the newly adopted endpoint reported separately.
priorpins=pins['historical_reused_revisions']; roots=[(c['ref'],c['root']) for c in json.loads((B/'recount9/import-closures9.json').read_text())]
for k,_ in roots:
 if k not in revs:revs[k]=priorpins[k]
closures=[]
for k,root in roots+[('rw','PV_MEAS_Deployed')]:
 paths={root:[root]};queue=[root];missing=[]
 for m in queue:
  if not m.startswith(('R1Z.','R0Z.','PV_')):continue
  s,p=module(k,m)
  if s is None:missing.append(m);continue
  for d in re.findall(r'^import\s+(\S+)',s,re.M):
   if d not in paths:paths[d]=paths[m]+[d];queue.append(d)
 closures.append({'ref':k,'revision':revs[k],'root':root,'new_endpoint':root=='PV_MEAS_Deployed','paths':paths,'unresolved_project_modules':missing})
for r in rows:
 th=r.get('closure_theorem') if r['recount10_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  m=next((r.get('closure_source_module'+str(i)) for i in [9,8,7,6] if r.get('closure_source_module'+str(i))),None)
  if r['id'] in restores:m='.'.join(th.split('.')[:2])
  m=m or ('.'.join(th.split('.')[:2]) if th.startswith('R1Z.') else th.split('.')[0])
 else:
  d=r.get('definition','').split('#')[0];m=('R1Z.'+Path(d).stem if '/lean/prover-rw-' in d else d.split('/lean/')[-1][:-5].replace('/','.')) if '/lean/' in d and d.endswith('.lean') else None
 ws=[];new=[]
 if m:
  source,p=module('rw',m)
  if th:
   assert source is not None,(r['id'],m)
   r['closing_statement10']={'ref':'rw','revision':revs['rw'],'module':m,'path':p,'sha256':hashlib.sha256(source.encode()).hexdigest(),'theorem':th}
  for cl in closures:
   if m not in cl['paths']:continue
   s,_=module(cl['ref'],m)
   norm=lambda t:re.sub(r'^import[^\n]*\n','',t,flags=re.M)
   if not th or (s and source and norm(s)==norm(source)):
    w={'ref':cl['ref'],'root':cl['root'],'path':cl['paths'][m],'scope':'import membership, not discharge'}
    (new if cl['new_endpoint'] else ws).append(w)
 r['import_witnesses10']=ws;r['event_endpoint_import_witnesses10']=new
 r['in_headline_closure10']='research' if any(w['ref']=='research' for w in ws) else 'candidate' if ws else 'neither'
 if r['recount10_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in 'abcd'
(P/'import-closures10.json').write_text(json.dumps(closures,separators=(',',':'))+'\n')
(P/'rows10.json').write_text('[\n'+',\n'.join(json.dumps(r,separators=(',',':')) for r in rows)+'\n]\n')
t={'rows':len(rows),'classes':dict(collections.Counter(r['recount10_class'] for r in rows)),'statuses':dict(collections.Counter(r['recount10_status'] for r in rows)),'open_dependencies':dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount10_status']=='OPEN')),'all_row_imports':dict(collections.Counter(r['in_headline_closure10'] for r in rows)),'restored':list(restores),'status_changes':[{'id':r['id'],'before':r['recount9_status'],'after':r['recount10_status'],'reason':r['recount10_basis']} for r in rows if r['recount9_status']!=r['recount10_status']],'bucket_changes':[{'id':r['id'],'before':r['recount9_bucket'],'after':r['dependency_bucket'],'reason':r['recount10_basis']} for r in rows if r['recount10_status']=='OPEN' and r['recount9_bucket']!=r['dependency_bucket']],'k3_credits':kcounts,'endpoint_premises_removed_added_weakened':[0,0,0],'consumer_premises_removed':['QueryAppend','FinishContext'],'Lean':0,'Kani':0,'target':'Target not yet established'}
(P/'totals.json').write_text(json.dumps(t,indent=2)+'\n')
ls=['# Recount 10 2026-11-02 (B)','','All407 rows. Historical fields remain verbatim in rows10.json; current text supersedes dated dispositions. Membership is not discharge. Target not yet established.','','| Row / class9 →10 / name | Status9 →10 | OPEN bucket | in headline closure? | Tool trust | Derivation, residual and evidence |','|---|---|---|---|---|---|']
for r in rows:
 detail=r['recount10_basis']+' Residual: '+r['residual10']+' Full evidence: recount10/rows10.json#'+r['id']
 ls.append('|'+r['id']+' / '+r['recount9_class']+' → '+r['recount10_class']+' / '+r['name'].replace('|','\\|')+'|'+r['recount9_status']+' → '+r['recount10_status']+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure10']+'|'+r['tool_trust10']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(B/'ROWS10.md').write_text('\n'.join(ls)+'\n');(P/'pins.json').write_text(json.dumps(pins,indent=2)+'\n');save();print(json.dumps({k:v for k,v in t.items() if k not in ['status_changes','bucket_changes']},indent=2))
