from auditlib8 import *
rows=json.loads((B/'recount7/rows7.json').read_text());by={r['id']:r for r in rows};da={x['id']:x for x in json.loads((P/'definition-audit8.json').read_text())}
for r in rows:
 r['recount8_status']=r['recount7_status'];r['recount8_class']=r['recount7_class'];r['recount7_bucket']=r['dependency_bucket'];r['definition_witnesses8']='definition-audit8.json#'+r['id']+'/sources';r['definition_changed8']=da[r['id']]['changed_from7'];r['recount8_evidence']=['definition-audit8.json#'+r['id'],'../recount7/rows7.json#'+r['id']]
 r['recount8_basis']='Pinned full defining source and prior scoped statement derivation retained. '+r['recount7_basis']
 r['residual8']=r['residual7'];r['tool_trust8']='RECLASSIFICATION within existing Kani/Charon/Aeneas tool trust where native semantic transport is used; no premise removal' if (r['recount7_status']=='CLOSED-ON-CANDIDATE' or int(re.sub('[^0-9]','',r['id']) or 0) in range(152,272)) else 'No new native tool-semantic transport credited; prior named trust/premises retained'
 r['native_disposition8']='Prior scoped evidence retained; not new deployment discharge'
def update(id,basis,status=None,bucket=None,theorem=None,route=None,module=None,ev=(),res=None):
 r=by[id];r['recount8_basis']=basis;r['recount8_evidence']+=list(ev)
 if status:r['recount8_status']=status
 if bucket:r['dependency_bucket']=bucket
 if theorem:r['closure_theorem']=theorem
 if module:r['closure_source_module8']=module
 if route:r['closure_route']=route
 if res:r['residual8']=res
common='E1/E2, real native RunJoin/carrier/world V165–V167, compiler/executable and retained runtime/allocator primitive adequacy, proof-account client route and L1/L2/L3 remain. No endpoint premise removed; tool-semantic transport is RECLASSIFICATION.'
suspended='164 169 170 178 181 182 183 184 186 187 195 198 201 216 219 220 221 222 229 230 231 233 236 238 239 240 242 247 256 257 258 259 260 265 197 212 213 217 218 237 246'.split();suspended=['V'+x.zfill(3) for x in suspended];assert len(set(suspended))==41
for id in suspended:
 update(id,'SUSPENDED deployed native-link credit by fscan/D386; earlier Lean/model/selected law remains historical evidence. '+common,status='OPEN',bucket='d' if id=='V197' else 'c' if id=='V242' else 'b',ev=['fscan:evidence/pv-fscan-20261028/CLASSIFY.md'],res=common)
 by[id]['native_disposition8']='SUSPENDED deployed association; original model/source theorem not refuted'
# Restorations: source/callback scopes, not generic whole machine laws.
restored={}
for id in ['V164','V170','V182','V183','V184','V186','V187','V195','V198','V219']:
 path='evidence/pv-rdb1-20261028/rows/'+id+'.json';x=json.loads(read('rw',path));restored[id]=dict(worker='rdb1',record=x,record_path=path,route='structural (K-1 substitute)',theorem=x['original_closing_theorem'])
for id in ['V238','V240','V247']:
 path='evidence/pv-rdb2-20261028/'+id+'.md';s=read('rw',path);th={'V238':'R1Z.PV_DL_CtSelected.selected_native','V240':'R1Z.PV_RDB2_Compress.complete','V247':'R1Z.PV_RDB2_SumDeployed.installed'}[id]
 restored[id]=dict(worker='rdb2',record=s,record_path=path,route='structural (K-1 substitute)',theorem=th)
for id in ['V169','V212','V216','V218','V221','V222','V246']:
 path='evidence/pv-rdcd-20261028/rows/'+id+'.json';x=json.loads(read('rw',path));th={'V169':'R1Z.PV_RDCD_TakeBinding.vector_m31','V212':'R1Z.PV_CB_Op107Exact.op107_source','V216':'R1Z.PV_RDCD_ContextInstall.op114_complete','V218':'R1Z.PV_RDCD_Op118Audit.source','V221':'R1Z.PV_RDCD_Audit.v221','V222':'R1Z.PV_RDCD_Audit.v222','V246':'R1Z.PV_RDCD_StatementBridge.source'}[id]
 restored[id]=dict(worker='rdcd',record=x,record_path=path,route='extraction with deployed source-law transport' if id not in ['V221','V222'] else 'structural dependency source/world',theorem=th)
for id in ['V258','V259']:
 path='evidence/pv-rdb2c-20261028/'+id+'.md';restored[id]=dict(worker='rdb2c',record=read('rw',path),record_path=path,route='structural (K-1 substitute)',theorem='R1Z.PV_RDB2C_FinalReplay.'+id.lower())
notes={
'V164':'All raw tag/values/lambda, complete ordered arithmetic Result; primitive operations remain explicit.',
'V170':'Only inventoried Vec<u32>/Global destructor, arbitrary returning free primitive and world. Generic all-T drop is refuted, not restored; fixed selected callback returns unit and other types retain old op4.',
'V182':'Every representable append buffer/tail, snapshot copy, first error before copy, updated header/private allocator world; no assumed allocation success.',
'V183':'Every type/layout/additional count under valid runtime shape; world-indexed callback family with explicit metadata/error encoding, allocation failure and post-header. This is not a fixed world-free native callback.',
'V184':'Generic non-Copy/ZST move, buffer ownership, unchanged allocation/frame; old copying-reference counterexample retained.',
'V186':'Generic same Vec::new constructor; empty length without falsely setting ZST capacity zero.',
'V187':'Generic owned Vec-to-array, mismatch retains input and finalization effects; no payload-copy assumption.',
'V195':'All raw limbs, all eight chunks exactly once, complete copy frame; ManuallyDrop restoration checked.',
'V198':'Arbitrary output length, ordered range errors and retained first eight bytes on later error.',
'V219':'All raw28 coefficients, explicit ordered complete-Result arithmetic and independent four-limb updates.',
'V238':'Generic Ct wrapper/default/copy; explicit finalizer/TRUNC_SIDE remain parameters, full32 and output-shape<=32.',
'V240':'All raw words and slice lengths; literal five emitted arithmetic operations, deployed prover_shared index-loop caller; extraction transport remains tool trust.',
'V247':'All slices; wrong length has no read, valid1024 cells with full storage and optimized fold/pointer law.',
'V169':'Four concrete Default dictionaries (M31/QM31 Vec and array10/16), no-allocation metadata/frame; not arbitrary native Default/Drop.',
'V212':'All raw QM31, complete Result/Option; exact original three literal typing adapters with proved U64 corrections; raw unadapted failure retained.',
'V216':'Complete bytewise32 comparison/carrier equality, separately bound source identity; not automatic credit for all compiler-lowering differences.',
'V218':'Complete three arrays and ordered iterator state/writeback, original two adapters and TrustedStep/Rev bounds; no dropped restoration.',
'V221':'Emitted byte-array dictionary, source association at recorded lengths32/64, ordered volatile writes followed by address-bearing assembly barrier. Native binary erasure not proved.',
'V222':'Emitted scalar/consuming Drop byte dictionaries, complete zeroize1.9.0 source/world trace. Old compilerFence trace superseded; not a hardware fence.',
'V246':'Every raw/noncanonical statement, full equality Result, exact indexed short-circuit source; initial extraction with two external axioms rejected.',
'V258':'Every weights/kappa and input-dependent resource outcome; public32768-byte alignment4 request once, null error before initialization,1024 restored cells. Failure/post-state explicit under rdea-1.',
'V259':'Every native variant/raw alpha/point; public2116-byte alignment4 Box request, null handler before initialization,2112 payload bytes plus variant, padding not claimed initialized. BoxAdequacy derived from retained primitive adequacy, not a new trust field.'}
for id,x in restored.items():
 th=x['theorem'];m='.'.join(th.split('.')[:2]) if th.startswith('R1Z.') else th.split('.')[0]
 update(id,'CONFIRM restoration at existing qualified selected source/library boundary. '+notes[id]+' '+common,status='CLOSED-ON-CANDIDATE',theorem=th,module=m,route=x['route'],ev=['rw:'+x['record_path'],'closure-audit8.json#'+id],res=common)
 by[id]['native_disposition8']='RESTORED scoped deployed source association; finite validation is not universal native execution';x.update(id=id,verdict='CONFIRM qualified restoration',hypotheses_nonvacuity_scope=notes[id],endpoint_premises_removed=0,tool_trust=by[id]['tool_trust8'])
# Additional intermediate packets that survive fscan at their scoped source boundary.
for id,th in {'V234':'R1Z.PV_DL_DigestFinal.selected_native','V235':'R1Z.PV_DL_FixedFinal.selected_native'}.items():
 update(id,'CONFIRM dlib2 selected wrapper structural packet; full Result, lossless carriers and nonvacuity, block compression/finalizer parameters explicitly retained. fscan STANDS at this parameterized boundary, not SHA-NI/native backend closure. '+common,status='CLOSED-ON-CANDIDATE',theorem=th,module='.'.join(th.split('.')[:2]),route='structural (K-1 substitute)',ev=['rw:evidence/pv-dlib-20261028/REPORT.txt'],res=common)
for id,m,th in [('V228','PV_B3P_Install132','reference'),('V243','PV_B3P_Closure226','complete_result')]:
 update(id,'CONFIRM selected structural source/value packet with complete Result and original carrier. '+('Entire ordered3803-cell/count loop, source predicates and capacity discharged; successful raw witness,261 other callbacks framed. Native same-unit comparison is finite.' if id=='V228' else 'Every raw public carrier, both variants; ordered1427/1455-byte layout and complete error paths, successful witnesses and original carriers; native pairs finite.')+' '+common,status='CLOSED-ON-CANDIDATE',theorem=m+'.'+th,module=m,route='structural (K-1 substitute)',ev=['rw:evidence/pv-b3p6-20261028/FINAL.md','rw:evidence/pv-b3p6-20261028/FINAL-D373.md'],res=common)
# The t finding deliberately reverses the lead's RESTORED claim.
update('V213','REJECT D403 restoration under ruling(t): sole exact-source PV_CB_Op109CanonicalBinding receipt41466 is a successful compile inside the180s cooldown. Final coherence lists only41466; downstream audits import its object and do not recompile it. Source/model laws are retained, no theorem-falsity claim. Compliant binding recompile plus dependent validation required.',status='OPEN',bucket='b',ev=['rw:evidence/pv-rdcd-20261028/RESUME-SEQUENCING.md','rw:evidence/pv-rdcd-20261028/resume-final-receipt-coherence.json','CORRECTIONS8.md'],res=common)
by['V213']['native_disposition8']='SUSPENDED; restoration rejected for void41466'
update('V242','OPEN c: class-A lowering-only same source remains pending owner decision on compiler-cohort/V370 boundary; fifth amendment does not itself approve this separate privacy choice.',status='OPEN',bucket='c',res=common)
for id in ['V178','V181']:
 update(id,'SUSPENDED. rdeac strengthens concrete literal69/clone-first handlers, physical world/frame and owned cleanup. No unconditional complete-Result publication-dictionary/native OOM equality. Diagnostic/indirect source provenance incomplete;61199 final endpoint replay failed, qualified correction uncompiled. Void60309 was compliantly recompiled61101, which does not close remaining obligations. No checked witness-dependent event/text finding.',status='OPEN',bucket='b',ev=['rw:evidence/pv-rdeac-20261028/REPORT.md','rw:evidence/pv-rdeac-20261028/diagnostic-provenance.json'],res=common+' Complete native diagnostic provenance and successful coherent endpoint replay remain.')
for id in ['V229','V230','V231','V239','V256','V257']:
 update(id,'SUSPENDED at pinned rdb2d head. Complete resource/value/restoration models and finite native checks do not supply the native typed byte-memory/ownership/iterator/mutable-handle instance; REPORT.md retains each exact blocker. Passing61097–61099 model audits are not whole-row restoration.',status='OPEN',bucket='b',ev=['rdb2d:evidence/pv-rdb2d-20261028/REPORT.md'],res=common)
for id in ['V197','V201','V217','V220','V233','V236','V237','V260','V265']:
 update(id,'SUSPENDED. Pinned rdcd3 contains supporting concrete library/source-loop work; REPORT.md and STATUS retain all nine rows. No complete deployed binding/instance or restored row. Pin/projection tools cannot stand in for missing original checkers; structural route under rdcd3-1 needs complete deployed-body binding. '+('Pinned extraction escaping-reference/loan validation is exact obstruction.' if id=='V197' else 'V265 pointer-form Kani remains quarantined; static form conditions are not inferred.' if id=='V265' else 'Unresolved library/world/carrier instance remains.'),status='OPEN',bucket='d' if id=='V197' else 'b',ev=['rdcd3:evidence/pv-rdcd3-20261028/REPORT.md'],res=common)
for id in ['V241','V245','V244']:
 update(id,'OPEN: pinned b3p6 supporting component/emission/installation laws do not finish selected callback source association. V244 still needs full reference/callback success nonvacuity, exhaustive structural binding, remaining D188 and accumulator comparison, slice-caller and pre-inline std coverage. core::fmt vtable glue invocation classification is under D348. Conditional op227 RunJoin premise not discharged.',status='OPEN',bucket='d' if id=='V241' else 'b',ev=['b3p6:evidence/pv-b3p6-20261028/resume7/RESIDUALS.md'],res=common)
for id in ['V152','V153','V154']:
 update(id,'Original REDUCED raw-family handoff retained: identification conjunction unsatisfiable through build_eq, not three false equations. HonestIdentification26 discharges the separate honest family. CanonicalHonest31 and CanonicalCoverage31 now derive HonestInput on every successful codec-first preparation and characterize that route; runjoin33 repairs coherent endpoint/lane/snapshot audits. Neither raw cached family nor deployed RustRealRefinement is thereby proved. Positive change necessary in both spend kinds; owner domain choice remains open.',ev=['runjoin:evidence/pv-runjoin31-20261028/OWNER-COVERAGE.md','runjoin:evidence/pv-runjoin33-20261028/REPORT.md'],res=common)
for id in ['V038','V045','V046','V047','V163','V165','V167']:
 update(id,'Prior status retained. Runjoin33–46 source body/serialization/caller proofs do not establish full native observation/ROMView decoders/helper effects/RustRealRefinement. rjdec lower criteria and repaired zeroize law do not constitute complete native decoder installation. V047 has headline-carrier public/canonical witness/payment/lane partial results; native handle/decoder and exact joint-wrapper association remain. D415: JHx_Joint.source is historical-forest evidence only, not headline satisfiability; no retargeted joint witness credited. FixturePdaRuntime deferred, not discharged.',ev=['rw:evidence/pv-2tnv-20261028/REPORT.md','rjdec:evidence/pv-rjdec-20261028/REPORT.md','CORRECTIONS8.md'],res=common)
for id in ['V347','V348','V349','V350','V351','V352','V353','V354','V355','V356','V357','V358','V359','V360','V361','V362','V363','V364','V365']:
 update(id,'OPEN b. Canonical decode/honesty, event/guard/parser/trace helper proofs and no checked honest leak do not establish whole native observer/failure-state coupling. Retain all L1/L2 and actual caller/RunJoin dependencies; D375 confines noncanonical-limb counterexample to bypassing direct library callers.',ev=['CORRECTIONS8.md'],res=common)
for id in ['V340','V373','V374']:
 update(id,'Prior OPEN bucket retained. Empty shipped-source diff to82566acdfb supports stage-A ELF/client/fixture/1000-pair evidence reuse; no new final theorem/release association. D359 clean ten-pair timing is all throttled: pre-registered unthrottled gate undecided, owner acceptance of paired throttled data remains pending. N2–N6/native L2 and DOITM physical transfer remain.',ev=['CORRECTIONS8.md'],res=common)
for id in ['V268','V269','V270','V396']:
 by[id]['recount8_basis']+=' D348 coverage gap includes deployed verifier and client formatting/error/backtrace channels; occurrence/content witness dependence is unproved, no checked witness pair leak. D414 core::fmt and rdeac diagnostic evidence do not close a total deployed observation encoding. D416 requires deployed verifier equals pinned release ELF; historical fb2fc048 is not the release. Client scope remains owner decision.'
# Scope-specific theorem source membership from exactly the recount7 consumer roots.
def mod(k,m):
 s,path=module(k,m)
 if s is None and m.startswith('PV_B3P_'):path='evidence/pv-b3p6-20261028/lean/'+m+'.lean';s=read(k,path)
 return s,path
roots=[('research','R1Z.PrivacyR1HeadlineDeployedReal'),('join','R1Z.PV_Join_Wire_FinalAuditA'),('join','R1Z.PV_Join_PublicCaller'),('rw','R1Z.ProverRw19CanonicalAuditRefinement'),('rw','R1Z.ProverRw18ContextData'),('rw','R1Z.PV_Op223_V164'),('rw','R1Z.PV_Join_Wire_FinalAuditA'),('rw','R1Z.PV_Join_PublicCaller')]
closures=[]
for k,root in roots:
 paths={root:[root]};queue=[root];unresolved=[]
 for m in queue:
  if not m.startswith(('R1Z.','R0Z.','PV_B1_','PV_B3_','PV_B3P_')):continue
  s,path=mod(k,m)
  if s is None:unresolved.append(m);continue
  for d in re.findall(r'^import\s+(\S+)',s,re.M):
   if d not in paths:paths[d]=paths[m]+[d];queue.append(d)
 closures.append(dict(ref=k,root=root,paths=paths,unresolved_project_modules=unresolved))
statements=[]
for r in rows:
 ws=[];id=r['id'];th=r.get('closure_theorem') if r['recount8_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  m=r.get('closure_source_module8') or r.get('closure_source_module7') or r.get('closure_source_module6') or ('.'.join(th.split('.')[:2]) if th.startswith('R1Z.') else th.split('.')[0]);s,path=mod('rw',m)
  assert s is not None,(id,th,m)
  r['closing_statement8']=dict(ref='rw',module=m,path=path,sha256=hashlib.sha256(s.encode()).hexdigest(),theorem=th)
  statements.append(dict(id=id,**r['closing_statement8']))
  norm=lambda s:re.sub(r'^import[^\n]*\n','',s,flags=re.M)
  for c in closures:
   if m in c['paths']:
    t,p=mod(c['ref'],m)
    if t and norm(t)==norm(s):ws.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][m],scope='identical closing law source; not deployment discharge'))
 elif id!='V270':
  d=r.get('definition','').split('#')[0]
  if '/lean/' in d and d.endswith('.lean'):
   m='R1Z.'+Path(d).stem if '/lean/prover-rw-' in d else d.split('/lean/')[-1][:-5].replace('/','.')
   for c in closures:
    if m in c['paths']:ws.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][m],scope='defining-source membership only'))
 r['in_headline_closure8']='research' if any(x['ref']=='research' for x in ws) else 'candidate' if ws else 'neither';r['import_witnesses8']=ws
 if r['recount8_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in 'abcd'
(P/'closure-audit8.json').write_text(json.dumps(list(restored.values())+[dict(id='V213',verdict='REJECT restoration; void41466',evidence='CORRECTIONS8.md')],indent=1)+'\n')
(P/'closing-source-index8.json').write_text(json.dumps(statements,indent=1)+'\n')
(P/'import-closures8.json').write_text(json.dumps(closures,indent=1)+'\n');(P/'manifest.json').write_text(json.dumps(manifest,indent=1)+'\n');(P/'rows8.json').write_text('[\n'+',\n'.join(json.dumps(x,separators=(',',':')) for x in rows)+'\n]\n')
t=dict(rows=len(rows),classes=dict(collections.Counter(r['recount8_class'] for r in rows)),statuses=dict(collections.Counter(r['recount8_status'] for r in rows)),open_dependencies=dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount8_status']=='OPEN')),closure_routes=dict(collections.Counter(r.get('closure_route') for r in rows if r['recount8_status']=='CLOSED-ON-CANDIDATE')),all_row_imports=dict(collections.Counter(r['in_headline_closure8'] for r in rows)),candidate_closure_imports=dict(collections.Counter(r['in_headline_closure8'] for r in rows if r['recount8_status']=='CLOSED-ON-CANDIDATE')),restorations_accepted=len(restored),restorations_rejected=['V213'],suspended=[id for id in suspended if by[id]['recount8_status']=='OPEN'],premises_removed_added_weakened=[0,0,0],Lean=0,Kani=0)
(P/'totals8.json').write_text(json.dumps(t,indent=2)+'\n')
ls=['# Recount 8 2026-10-28 (B)','','All407 rows retain historical scope; immutable statements, source bodies, audit receipts and native classes are indexed by recount8/manifest.json. Fifth-amendment tool-trust tag never denotes premise removal. Target not yet established.','','| Row / class7 →8 / name | Status7 →8 | OPEN bucket | in headline closure? | Tool trust | Derivation, residual and evidence |','|---|---|---|---|---|---|']
for r in rows:
 detail=r['recount8_basis']+' Residual: '+r['residual8']+' Full witnesses: recount8/rows8.json#'+r['id'];ls.append('|'+r['id']+' / '+r['recount7_class']+' → '+r['recount8_class']+' / '+r['name'].replace('|','\\|')+'|'+r['recount7_status']+' → '+r['recount8_status']+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure8']+'|'+r['tool_trust8']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(B/'ROWS8.md').write_text('\n'.join(ls)+'\n');print(json.dumps(t,indent=2))
