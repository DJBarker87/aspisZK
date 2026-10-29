from auditlib9 import *
rows=json.loads((B/'recount8/rows8.json').read_text());by={r['id']:r for r in rows};da={x['id']:x for x in json.loads((P/'definition-audit9.json').read_text())}
common='E1/E2, real native RunJoin/carrier/world V165–V167, compiler/executable V370/D381/D386, retained runtime/allocator adequacy rdea-1, proof-account client and L1/L2/L3 remain. No endpoint premise removed; tool-semantic transport remains reclassification.'
for r in rows:
 for suffix in ['status','class','basis']:r['recount9_'+suffix]=r['recount8_'+suffix]
 r['recount8_bucket']=r['dependency_bucket'];r['definition_witnesses9']='definition-audit9.json#'+r['id'];r['definition_changed9']=da[r['id']]['changed_from8'];r['residual9']=r['residual8'];r['tool_trust9']=r['tool_trust8'];r['recount9_evidence']=['definition-audit9.json#'+r['id'],'../recount8/rows8.json#'+r['id']]
 r['recount9_basis']='Re-derived at pinned defining source; prior scoped derivation retained. '+r['recount8_basis'];r['native_disposition9']=r['native_disposition8']
def update(id,basis,status=None,th=None,mod=None,route=None,ev=(),bucket=None):
 r=by[id];r['recount9_basis']=basis;r['recount9_evidence']+=list(ev)
 if status:r['recount9_status']=status
 if th:r['closure_theorem']=th
 if mod:r['closure_source_module9']=mod
 if route:r['closure_route']=route
 if bucket:r['dependency_bucket']=bucket
restores={
'V229':('R1Z.PV_OWNH_Literals.v229_result','R1Z.PV_OWNH_Literals',"exhaustive over a singleton input domain, deployed-configuration harness",'ownh','Constant 214-word sorted rows; 437 canonical Result bytes. Whole ordinary cone influence/address argument, allocator-write channel closed; allocator failure and process timing are retained, not singleton observables.'),
'V230':('R1Z.PV_OWNH_Literals.v230_result','R1Z.PV_OWNH_Literals',"exhaustive over a singleton input domain, deployed-configuration harness",'ownh','Constant64-word masks;137 canonical Result bytes; row/mask expansion and original fingerprint agree. V229 dependency and local shifts/array indexing are bound at the same qualified boundary.'),
'V256':('R1Z.PV_RDB2F_SamplerCalls.gamma_callback','R1Z.PV_RDB2F_SamplerCalls','structural (K-1 substitute)','rdb2h','Original gamma reverse iterator/current-array/FnMut restoration, optional second carry and original verifier continuation; exact original LEAN_PATH 88-target replay completed, no object-hash differences.'),
'V257':('R1Z.PV_RDB2F_SamplerCalls.ordinary_callback','R1Z.PV_RDB2F_SamplerCalls','structural (K-1 substitute)','rdb2h','Original from_fn/ordinary iterator and all eight writes plus final returned quotient before decode/caller; same exact-environment replay, no new extractor or fixture proof.'),
'V260':('R1Z.PV_RDCD3_V260Complete.complete','R1Z.PV_RDCD3_V260Complete','structural (K-1 substitute)','rdcd3','Both original253 and selected251 APIs, all weights/kinds/indices, complete Result/errors/divergence; source range/fold/index bindings, no replacement checker credited.'),
'V265':('R1Z.PV_RDCD3_V265.complete','R1Z.PV_RDCD3_V265','structural (K-1 substitute)','rdcd3','All block/row inputs, static circle control and concrete M31 inverse including zero assertion; pointer-form Kani remains quarantined. No arbitrary inverse or success premise.'),
'V217':('R1Z.PV_RDCD3_V217.complete','R1Z.PV_RDCD3_V217','structural (K-1 substitute)','rdcd3','All typed c1/mask/g/point; complete source-shaped selected-mask/owned Result equality, every updated array; source/field/reverse library mapping separately checked. Optional totality draft not credited.'),
'V213':('R1Z.PV_RDCD_Op109Audit.source','R1Z.PV_RDCD_Op109Audit','extraction with deployed source-law transport','fix','All raw WideExact x, complete Result/Option with ExternalTypes/ExternalFuns retained. Binding62012, Funs/Exact62013–62014, restoring source62112 and focused source/reference/op109_source audit62113 compliantly rebuilt. Void41466 remains excluded. Seventeen aggregate consumers are unfinished; that blocks aggregate release replay, not this scoped row credit.')}
for id,(th,m,route,w,scope) in restores.items():
 update(id,'CONFIRM qualified restoration. '+scope+' '+common,status='CLOSED-ON-CANDIDATE',th=th,mod=m,route=route,ev=['rw:evidence/pv-'+w+'-'+('20261028' if w in ['fix','rdcd3'] else '20261029')+'/REPORT.md','independent-audit9.json#'+id,'CORRECTIONS9.md'])
 by[id]['native_disposition9']='RESTORED qualified selected source/value association; no whole deployed observation claim';by[id]['residual9']=common
# Exact pending owner action takes c precedence over a missing native instance.
update('V231','OPEN c. Concrete software SHA path established; reachable SHA-NI path conditional on SHA_NI_IntrinsicsSemantics (per-instruction equations, not the finalizer conclusion). Owner backend/instruction decision remains pending; no new T field. '+common,bucket='c',ev=['rw:evidence/pv-rdb2f-20261029/V231.md'])
update('V239','PARTIAL, still OPEN b. PV_OWNM_V239.restore decomposes dense value plus public resource trace into ActualInput, SourceDense, Transcript879, Transcript890 and OwnedPublicPlan. SourceDense proved; ActualInput composed only at source stage, deployed association remains. Other deployed links remain open. Ownp finite comparisons do not instantiate them. Line PARKED after ownp; skeleton and definitions retained unchanged.',ev=['rw:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_OWNM_V239.lean','rw:evidence/pv-ownp-20261029/REPORT.md'])
for id in ['V178','V181']:
 update(id,'OPEN b, parked under D348. Rdeac final replay now passes62002 after name repair (D423), so recount8 uncompiled61199 correction is no longer the blocker. DIAG models and syscall/buffering laws remain conditional; std I/O/format/capture/cleanup deployed association and joint occurrence/operand/frame laws remain. Diagnostic line PAUSED D479 pending owner D474; no checked honest witness-dependent diagnostic found.',ev=['rw:evidence/pv-fix-20261028/REPORT.md','rw:evidence/pv-diag12-20261029/REPORT.md'])
for id in ['V241','V244','V245']:
 update(id,'OPEN; op227 bridge PARTIAL/in progress at pinned b3p6 head. 36/79 conservative candidates reclassification-bound to immutable raw extraction under b3p6-1; seven token-identical spans lack model declarations,36 nonidentical candidates remain. Token identity is no complete library/caller/port binding. D188 per-function/matrix checks, slice bounds/std coverage and unconditional selected_callback remain. V244 residual(a) full composition_parts and reference/installed-callback nonvacuity is settled at emitted/original-carrier scope (D432); it is not native closure.',ev=['b3p6:evidence/pv-b3p6-20261028/resume12/RESIDUALS.md','independent-audit9.json#b3p6-1'])
for id in ['V038','V045','V046','V047','V163','V165','V167','V268','V269','V270','V396']:
 by[id]['recount9_basis']+=' D476/D478: current Runtime.disclosed/observerOracle consume only returned Result; native event observation does not factor through it. Post-computation prove_wall_seconds changes with a finite pause on a good completed path while core Output/public/coins/option-B signal stay fixed. Conditional source/clock obstruction, no certified native non-bad pair and no privacy leak. Existing headline is Result-only, not full D159 joint privacy. Event-retaining extension requires owner D478; pinned evhd is experimental, not adopted. The byte-pinned typed caller statement equality and V047 fibre consumption are proved by rj4idb without an equality hypothesis; live native record/handle, joint wrapper and RustRealRefinement remain open.'
 by[id]['recount9_evidence']+=['rw:evidence/pv-fib-20261029/REPORT.md','rw:evidence/pv-top-20261029/LINKS.md']
for id in ['V347','V348','V349','V350','V351','V352','V353','V354','V355','V356','V357','V358','V359','V360','V361','V362','V363','V364','V365','V367']:
 by[id]['recount9_basis']+=' PARTIAL trace decomposition only. L1_COUNT_TRACE through candidate l1g has CountAcquisition (partial), BodyWrapper (open), OriginalRetry (partial), NativeD163/simE/Sites (open); no full native link closes. DIAG three skeletons retain fifteen named links; no owned deployed link discharged through diag12. L2E pinned preparation has no completed site instance; V361–V365 unproved. No independent coins, new charged event or success conditioning.'
for id in ['V045','V046','V047','V165','V167']:
 by[id]['recount9_basis']+=' RUNJOIN_PUBLISH_COMPACT skeleton at66904 has R24Sampler discharged; CommonSample, BackendInput, FinishContext, QueryAppend, NodeAppend and PublishOrder remain open at recorded54 result. Source-slice conditional publication is not full native/toRP composition. Rjdec parked; its caller-supplied decoder clauses do not install a deployed observer.'
# Preserve all historical classes and exact d/c/b/a buckets except explicit owner re-bucketing.
roots=[(c['ref'],c['root']) for c in json.loads((B/'recount8/import-closures8.json').read_text())];closures=[]
for k,root in roots:
 paths={root:[root]};queue=[root];unresolved=[]
 for m in queue:
  if not m.startswith(('R1Z.','R0Z.','PV_B1_','PV_B3_','PV_B3P_')):continue
  s,path=module(k,m)
  if s is None:unresolved.append(m);continue
  for d in re.findall(r'^import\s+(\S+)',s,re.M):
   if d not in paths:paths[d]=paths[m]+[d];queue.append(d)
 closures.append(dict(ref=k,root=root,paths=paths,unresolved_project_modules=unresolved))
statements=[]
for r in rows:
 ws=[];id=r['id'];th=r.get('closure_theorem') if r['recount9_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  m=next((r.get('closure_source_module'+str(i)) for i in [9,8,7,6] if r.get('closure_source_module'+str(i))),None) or ('.'.join(th.split('.')[:2]) if th.startswith('R1Z.') else th.split('.')[0]);s,path=module('rw',m);assert s is not None,(id,th,m)
  r['closing_statement9']=dict(ref='rw',module=m,path=path,sha256=hashlib.sha256(s.encode()).hexdigest(),theorem=th);statements.append(dict(id=id,**r['closing_statement9']))
  norm=lambda s:re.sub(r'^import[^\n]*\n','',s,flags=re.M)
  for c in closures:
   if m in c['paths']:
    t,p=module(c['ref'],m)
    if t and norm(t)==norm(s):ws.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][m],scope='identical closing law source, not deployment discharge'))
 elif id!='V270':
  d=r.get('definition','').split('#')[0]
  if '/lean/' in d and d.endswith('.lean'):
   m='R1Z.'+Path(d).stem if '/lean/prover-rw-' in d else d.split('/lean/')[-1][:-5].replace('/','.')
   for c in closures:
    if m in c['paths']:ws.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][m],scope='defining-source membership only'))
 r['in_headline_closure9']='research' if any(x['ref']=='research' for x in ws) else 'candidate' if ws else 'neither';r['import_witnesses9']=ws
 if r['recount9_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in 'abcd'
(P/'import-closures9.json').write_text(json.dumps(closures,indent=1)+'\n');(P/'closing-source-index9.json').write_text(json.dumps(statements,indent=1)+'\n');(P/'rows9.json').write_text('[\n'+',\n'.join(json.dumps(r,separators=(',',':')) for r in rows)+'\n]\n');save()
t=dict(rows=len(rows),classes=dict(collections.Counter(r['recount9_class'] for r in rows)),statuses=dict(collections.Counter(r['recount9_status'] for r in rows)),open_dependencies=dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount9_status']=='OPEN')),all_row_imports=dict(collections.Counter(r['in_headline_closure9'] for r in rows)),candidate_closure_imports=dict(collections.Counter(r['in_headline_closure9'] for r in rows if r['recount9_status']=='CLOSED-ON-CANDIDATE')),restored=list(restores),endpoint_premises_removed_added_weakened=[0,0,0],Lean=0,Kani=0)
(P/'totals9.json').write_text(json.dumps(t,indent=2)+'\n')
ls=['# Recount 9 2026-10-29 (B)','','All407 historical rows re-derived from immutable sources and scoped evidence. Membership is not discharge. Target not yet established.','','| Row / class8 →9 / name | Status8 →9 | OPEN bucket | in headline closure? | Tool trust | Derivation, residual and evidence |','|---|---|---|---|---|---|']
for r in rows:
 detail=r['recount9_basis']+' Residual: '+r['residual9']+' Full witnesses: recount9/rows9.json#'+r['id'];ls.append('|'+r['id']+' / '+r['recount8_class']+' → '+r['recount9_class']+' / '+r['name'].replace('|','\\|')+'|'+r['recount8_status']+' → '+r['recount9_status']+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure9']+'|'+r['tool_trust9']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(B/'ROWS9.md').write_text('\n'.join(ls)+'\n');print(json.dumps(t,indent=2))
