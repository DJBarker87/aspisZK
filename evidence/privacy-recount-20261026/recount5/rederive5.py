from pathlib import Path
import json,re,subprocess,hashlib,collections,os
P=Path(__file__).resolve().parent;B=P.parent
pins=json.loads((P/'pins.json').read_text())['revisions'];manifest=json.loads((P/'manifest.json').read_text());ix={(x['ref'],x['path']):x for x in manifest};used=set()
def read(k,path):
 used.add((k,path));x=ix.get((k,path))
 if x:return (P/x['snapshot']).read_text()
 q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True)
 if q.returncode:return None
 raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();out=P/'objects'/(blob+'.txt');out.parent.mkdir(exist_ok=True);out.write_bytes(raw)
 x=dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(out,P));ix[k,path]=x;manifest.append(x);return raw.decode()
R='docs/research/v8-r0-zk-20261009/lean/'
def module(k,m):
 path=R+m.replace('.','/')+'.lean';s=read(k,path)
 if s is None and m.startswith('R1Z.ProverRwFull'):
  path='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean';s=read(k,path)
 return s,path
rows=json.loads((B/'recount4/rows4.json').read_text());by={r['id']:r for r in rows};audit=json.loads((P/'definition-audit5.json').read_text());ad={a['id']:a for a in audit}
for r in rows:
 r['recount4_bucket']=r['dependency_bucket'];r['recount5_status']=r['recount4_status'];r['recount5_class']=r['recount4_class']
 r['definition_witnesses5']=ad[r['id']]['sources'];r['recount5_evidence']=['definition-audit5.json#'+r['id'],'../recount4/rows4.json#'+r['id']]
 r['recount5_basis']='Pinned definition/guards re-read; unchanged scopes retain the recount-4 derivation and residual. '+r['recount4_basis']
 # Compare defining bytes to all previous variants rather than just a branch label.
 r['definition_changed5']=[x['ref'] for x in ad[r['id']]['sources'] if x['ref'] not in ad[r['id']]['same_as_recount4']]
 if r['recount4_status']=='CLOSED-ON-RESEARCH':
  th=r.get('theorem','').split(' + ')[0];s,path=module('research','.'.join(th.split('.')[:2]));assert s,(r['id'],th)
  r['research_closure_statement5']=dict(theorem=th,path=path,sha256=hashlib.sha256(s.encode()).hexdigest());r['recount5_basis']='Research model theorem re-read at its exact guards/quantifiers; no deployed instance inferred. '+r['recount5_basis']
def update(id,why,status=None,bucket=None,th=None,route=None,ev=(),fields=None):
 r=by[id];r['recount5_basis']=why;r['recount5_evidence']+=list(ev)
 if status:r['recount5_status']=status
 if bucket:r['dependency_bucket']=bucket
 if th:r['closure_theorem']=th
 if route:r['closure_route']=route
 if fields is not None:r['residual_fields']=fields
# Re-read callback table and all closing laws, including the arbitrary carrier op51 law.
cb=read('cb','evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md');closed=[]
for line in cb.splitlines():
 if 'ROW-DISCHARGED(candidate)' not in line:continue
 c=line.split('|');op=int(c[1]);id=c[2].strip();th=c[4].strip();r=by[id];assert re.match('op'+str(op)+r'\b',r['name'])
 s,path=module('cb','.'.join(th.split('.')[:2]));assert s and th.split('.')[-1] in s
 update(id,'Direct extracted-source complete-Result law re-read at arbitrary declared inputs; native ABI/effects/deployment association retained.',th=th,ev=['cb:'+path,'cb:evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md']);closed.append(id)
assert len(closed)==23
for id,op in [('V219',120),('V242',225),('V254',246),('V195',51)]:
 m='R1Z.PV_CB3_Op'+str(op)+('Arbitrary' if op==51 else 'Source');s,path=module('cb3',m);assert s and 'op'+str(op)+'_source' in s
 update(id,by[id]['recount4_basis']+' Re-read current CB3 source and retained full carrier/Result scope; op229 overlaps CB and is counted once.',ev=['cb3:'+path])
# Seven library rows; the two new laws use their exact bounded native gates.
ops=read('cblib','evidence/pv-cblib-20261027/OPS.md');bundle,path=module('cblib','R1Z.PV_CBL_AppendBundle');assert bundle
for op,id in [(25,'V177'),(28,'V179'),(29,'V180'),(30,'V181'),(31,'V182'),(34,'V185'),(35,'V186')]:
 assert re.search(r'\| '+str(op)+r' \| '+id+r' \| P6 \| SOURCE LAW SUPPLIED',ops)
 th='R1Z.PV_CBL_AppendBundle.op'+str(op)+'_source';assert th.split('.')[-1] in bundle
 why=by[id]['recount4_basis'] if op not in [30,31] else ('op30: extracted safe empty-byte reference; empty-only String representation adapter; native capacity/content gate n≤4. Allocation/world and unbounded deployed-toolchain association remain.' if op==30 else 'op31: extracted safe byte append with checked UInt8/U8 and UTF-8 transport; native valid UTF-8 initial length 2 plus tail length 1. Complete Result and size/decoding failure retained; source-image, allocation/world, separate toolchains and unbounded deployed association remain.')
 update(id,why+' All seven laws now published together; publication is not a native/deployed instance.',status='CLOSED-ON-CANDIDATE',route='P6 gate',th=th,ev=['cblib:'+path,'cblib:evidence/pv-cblib-20261027/OPS.md'])
for id in ['V164','V240']:
 m='R1Z.PV_Op223_'+('V164' if id=='V164' else 'Source');s,path=module('rw',m);assert s
 update(id,('Applied candidate extraction closes V240 with arbitrary-input complete Result, and the selected V164 bridge supplies P_source_p6. V164 retains exactly reservation and P_proof_bytes. Candidate is 0c9dc9a4cc, rebased with the proof-account route. Pre-rebase op223 ELF/fixture/1,000-pair gates passed; integrated candidate validation and final timing/adoption are not inferred. Two ledger scopes, one callback decrement.'),ev=['rw:'+path,'research:LOG D278/D282/D283'],fields=['reservation; P_proof_bytes'] if id=='V164' else None)
update('V232',by['V232']['recount5_basis']+' D273 actual SHA-NI dispatch path awaits owner semantics/trust versus soft-backend route decision; current capped T admits no extra instruction field.',bucket='c',ev=['research:LOG D273'])
# New exact escaping-reference findings, distinct from Drop-only/internal refusals.
inv=read('cb9','evidence/pv-cb9-20261027/INVENTORY.md')
for op,id in [(226,'V243'),(227,'V244'),(228,'V245'),(230,'V247'),(250,'V257'),(251,'V258')]:
 sec=inv.split('### op'+str(op)+' / '+id)[1].split('### ')[0];assert 'escaping reference output requires loan validation' in sec
 update(id,'Exact CB9 direct-root escaping-reference guard (whole dependency closure); structured Drop also reported where recorded. No source law; route(ii) emissions/probes do not discharge source/Result transport.',bucket='d',ev=['cb9:evidence/pv-cb9-20261027/INVENTORY.md'])
op134=read('op134','evidence/pv-op134-20261027/ROUTE-II.md');assert 'escaping reference output requires loan validation' in op134
update('V230','Reference side complete: full Result equations, 3,803-cell uniqueness/completeness, 214 ascending deduplicated rows and 1,024 mask bits. Direct shipped extraction has exact escaping-reference plus Drop refusal. No shipped/reference association; route(ii) addendum is proposed only.',bucket='d',ev=['op134:evidence/pv-op134-20261027/ROUTE-II.md','op134:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Op134_AuditClosure.lean'])
update('V265','CB9 SKIP(sibling) is not closure: current CB source table says OBSTRUCTED(P6 pending); PV_CB_Op259Exact is PREPARED only and fresh extraction/focused check pending. Definition of a selected dictionary and its reflexive source equation do not supply the missing native/reference gate. Keep OPEN; no extra callback decrement.',bucket='a',ev=['cb9:evidence/pv-cb9-20261027/ROWS.md','cb:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB_Op259Exact.lean','cb:evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md'])
for id in ['V247','V261','V264']:
 update(id,by[id]['recount5_basis']+' Batch1 repaired op254 as prover-local, restoring weights.rs; three rebuilt ELF pins match. At this pinned checkpoint Lean 0/100; extraction/source laws/shift nonfailure/pole verdict/fixtures/audit remain next. No closure from gate(a).',ev=['batch1:evidence/pv-batch1-20261027/REPORT.md','batch1:evidence/pv-batch1-20261027/MODULE-GATES.md'])
for id in ['V231','V232','V233','V234','V235','V236','V237','V238']:
 update(id,by[id]['recount5_basis']+' CBL now proves the complete owned fixed soft digest value/totality for arbitrary sized byte Slice, using byte-fold/padding/finalizer laws. Generic borrowed wrappers/Drop, actual SHA-NI/soft dispatch and native/compiler association remain OPEN. The soft timing projection is not an actual whole-prover gate failure; no instruction semantics added to capped T.',ev=['cblib:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CBL_DigestSoftSource.lean','cblib:design/PV-SHA-DISPATCH-20261027.md'])
for id in ['V163','V038','V045','V336','V337','V338','V339']:
 update(id,by[id]['recount5_basis']+' Records repairs 1–14 preserve the documented body semantics and ELF pins, but latest repair still fails internally (InterpReduceCollapse.ml:1991). No R_shipped extraction accepted. Source public binding/trace P remains constructed only; deployed P, fixture/general identification, compiler-return, transition, public binding and P∧T non-vacuity remain open; counts 2/8/6 unchanged.',ev=['runjoin:evidence/pv-runjoin14-20261027/REPAIRS.md','runjoin:evidence/pv-runjoin15-20261027/trust-audit-status.md'])
update('V340','Candidate 0c9dc9a4cc contains the research merge and proof-account route (D278), unlike recount4 candidate. Research rebase subtask is evidenced; original whole adoption/equivalence/release binding remains OPEN: integrated candidate gates and subsequent sibling changes are not supplied by the historical merge.',bucket='b',ev=['research:LOG D278/D282','rw:evidence/pv-rebase3-20261027/README.md'])
for id in ['V352','V354','V357','V360']:
 update(id,'L2 source-control/ideal laws now proved: scalar/rejection/count/cursor/refill identities; accepted scalar uniformity independent of rejection count; nonzero entropy-pair conditional law; conditional guard algebra. N2–N6 require native associations: padding/sum, canonical parser round-trip, inactive sets/balancing folds, helper multiset/inverse boundary, native oracle/interpolation/running claim. E1/E2 and deployed RunJoin/simE coupling remain; V371 only for physical timing transfer. No whole-row closure.',bucket='b',ev=['l2b:evidence/pv-l2b-20261027/PREMISES.md','l2b:evidence/pv-l2b-20261027/SITES.md'])
update('V373','A/B audits exist (toolchain unpinned): N1 leaks on historical non-CT recipe and is removed in recommended candidate CT path; N2–N6 are L2 invariant/native-association obligations. N7 is signing-key-seed CUSTODY, not privacy-witness leakage; prepared raw-pipe patch only. Transitive binary classification incomplete, final integrated release binary/recipe/toolchain not adopted. V373 stays OPEN.',bucket='c',ev=['l3:evidence/pv-l3-20261027/dual/AUDIT.md','n7:design/PV-N7-20261027.md','research:LOG D284'],fields=['final selected binary transitive call-site audit; native L2 associations and V371 timing transfer'])
update('V374','Dudect plan preregistered but not scheduled/run: release recipe/toolchain and final integrated candidate selection await owner action. Old fixture medians are not the final timing evidence. DOITM remains separately V371.',bucket='c',ev=['research:LOG D276/D278','l3:evidence/pv-l3-20261027/dual/AUDIT.md'])
update('V370',by['V370']['recount4_basis']+' D270 reopens the native CLIENT toolchain decision: moving stable is not an artifact pin. Exact compiler preservation remains proof work after selection.',bucket='c',ev=['research:LOG D270','research:design/RELEASE-LEDGER-20261025.md'],fields=['exact client compiler/flags selection; preservation remains P, no new T field'])
update('V396','Proof-account client route is now present on candidate and binary call graph (D278). Source pin is not a build pin or a user-wallet implementation: D284 client constructs fixtures internally. Owner scope/toolchain/recipe decisions precede actual caller/upload/signing/failure/retry observer binding. N7 retained under custody only; not counted against privacy.',bucket='c',ev=['research:LOG D270/D278/D284','n7:evidence/pv-n7-20261027/INVENTORY.md'])
update('V400','Option B adopted; round2 IndependentOffBad names only existing charged events, with unchanged simE, observer and bound. Conditional deployed synchronisation, first-draw failure and joint charged-event transport proved. Native reachable-state/public-verdict synchronization at fixed HOST_HASH and actual failure metadata association remain OPEN, as does endogenous B headline. Existing B theorem is fixed-signal only; no qualifying native counterexample.',bucket='b',ev=['research:LOG D262/D266','research:evidence/pv-optb-20261027/INDEPENDENCE.md'])
update('V403','Canonical producer facts and op121_arguments are proved over exact extracted prefix; reached_canonical retains P_NativePrefixBinding. Complete recursive caller transport failed and is not proved. Canonicality is a native-prefix/caller association obligation now, not completion from producer facts alone.',bucket='b',ev=['research:LOG D271'])
for id in ['V397','V398']:
 update(id,'D281 dry coherence replay at research b90540e01c: 672 project modules (537 reused, 135 compiled), no project proof failure; 3,905 theorem axiom queries, union propext/Classical.choice/Quot.sound. This is coherent research evidence, not final adopted candidate/release dependency closure and final artifact binding. Original release obligation retained OPEN.',bucket='b',ev=['research:LOG D281','research:evidence/pv-replay-20261027/REPORT.md'])
update('V271','File carrier source is absent on the requested current branches. Re-read retained research snapshot of the exact dict revision: type0_installed selects a nonnegative signed32 File carrier, not live-descriptor ownership or exactly-once Drop. Native nondeterministic I/O/world/ownership transport remains OPEN; no source variant is fabricated.',bucket='b',ev=['research:evidence/privacy-recount-20261026/recount2/dict/docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_FileCarrier.lean.txt'])
# Added deployment rows are scoped evidence obligations, without invented Lean definitions.
for id in ['V401','V402']:
 # Retained research snapshots resolve the prior finite measurement's original revision.
 paths=[x for x in by[id]['recount2_evidence']]
 for path in paths:
  full='evidence/privacy-recount-20261026/'+path
  assert read('research',full) is not None,(id,full)
  by[id]['recount5_evidence'].append('research:'+full)
 update(id,by[id]['recount4_basis']+' Historical finite rebase measurement re-read from its retained research snapshot; it is not the new integrated candidate gate.')
for id in ['V404','V405']:
 for path in ['evidence/pv-join-20261026/resume4/FINAL-REPORT.md','evidence/pv-join-20261026/resume5/FINAL-REPORT.md']:
  assert read('join',path) is not None
  by[id]['recount5_evidence'].append('join:'+path)
for id,k,m in [('V380-inversion','research','R1Z.PV_Inv_GuardCoupling'),('V400','research','R1Z.PV_OptB_OffBadJoin'),('V403','research','R1Z.PV_Canon_AuditFinal'),('V406','runjoin','R1Z.PV_RunJoin_TrustItems')]:
 text,path=module(k,m);assert text is not None
 by[id]['recount5_evidence'].append(k+':'+path)
# Route2 historical versus interim resume remains a diagnostic, not callback closure.
rt=read('route2','design/PV-ROUTE2-20261027.md');assert '4 accepted emissions, 16 refusals, 7 unmeasured' in rt
for r in rows:
 if r['recount5_status']=='OPEN' and r['group']=='O':
  r['recount5_evidence']+=['route2:design/PV-ROUTE2-20261027.md']
  r['recount5_basis']+=' Route(ii) original inventory 4 accepted/16 refused/7 unmeasured is historical; pinned Drop-free resume has interim carrier probes, no completed generic equivalence/adoption. Ruling(l) requires module gates, including programs/r1-cost-probe; cost-probe crate edges alone do not permit in-place editing.'
# Import graph and exact-law body audit: same consumers as recount4 plus actual applied candidate V164.
roots=[('research','R1Z.PrivacyR1HeadlineDeployedReal'),('join','R1Z.PV_Join_Wire_FinalAuditA'),('join','R1Z.PV_Join_PublicCaller'),('rw','R1Z.ProverRw19CanonicalAuditRefinement'),('rw','R1Z.ProverRw18ContextData'),('rw','R1Z.PV_Op223_V164')]
closures=[]
for k,root in roots:
 paths={root:[root]};queue=[root];unresolved=[]
 for m in queue:
  if not m.startswith(('R1Z.','R0Z.')):continue
  s,path=module(k,m)
  if s is None:unresolved.append(m);continue
  for dep in re.findall(r'^import\s+(\S+)',s,re.M):
   if dep not in paths:paths[dep]=paths[m]+[dep];queue.append(dep)
 closures.append(dict(ref=k,root=root,paths=paths,unresolved_project_modules=unresolved))
for r in rows:
 ws=[];th=r.get('closure_theorem') if r['recount5_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  m='.'.join(th.split('.')[:2]);own='rw' if r['id'] in ['V164','V240'] else 'cblib' if r['closure_route']=='P6 gate' and r['id']!='V195' else 'cb3' if r['id'] in ['V195','V219','V242','V254'] else 'cb'
  canonical,_=module(own,m);assert canonical and th.split('.')[-1] in canonical,(r['id'],th)
  # For pre-existing CBL rows, compare the same published theorem's original module too;
  # new combined publication is not fabricated as an actual consumer root.
  for c in closures:
   target,path=module(c['ref'],m) if m in c['paths'] else (None,None)
   norm=lambda s:re.sub(r'^import[^\n]*\n','',s,flags=re.M)
   if target and norm(target)==norm(canonical):ws.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][m],source_path=path,scope='identical theorem body; imports may differ'))
 elif r['id']!='V270':
  d=r.get('definition','').split('#')[0]
  if '/lean/' in d and d.endswith('.lean'):
   m='R1Z.'+Path(d).stem if '/lean/prover-rw-' in d else d.split('/lean/')[-1][:-5].replace('/','.')
   for c in closures:
    if m in c['paths']:ws.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][m],scope='defining-source membership only; not discharge'))
 r['in_headline_closure5']='research' if any(x['ref']=='research' for x in ws) else 'candidate' if ws else 'neither';r['import_witnesses5']=ws
 if r['recount5_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in ['a','b','c','d']
# Independently verify every edge of the same 27-row wire table.
wire=read('join','evidence/pv-join-20261026/wire/IMPORT-CHAIN.md');wireaudit=[]
for line in wire.splitlines():
 if not re.match(r'\| V\d+',line):continue
 c=line.split('|');id=c[1].strip();th=c[3].strip(' `');ms=re.findall(r'`([^`]+)`',c[4]);valid=True
 if id!='V270':
  for left,right in zip(ms,ms[1:]):
   text,_=module('join',left);valid=valid and text is not None and right in re.findall(r'^import\s+(\S+)',text,re.M)
  text,_=module('join',ms[-1]);valid=valid and text is not None and th.split('.')[-1] in text
 wireaudit.append(dict(id=id,theorem=th,modules=ms,edges_valid=valid));assert valid,id
assert len(wireaudit)==27
assert sum(by[x['id']]['in_headline_closure5']=='candidate' for x in wireaudit)==26
(P/'wire-audit5.json').write_text(json.dumps(wireaudit,indent=2)+'\n')
# Resolve every current evidence file, not just its label; preserve explicit gaps.
evidence_audit=[]
for r in rows:
 for ev in r['recount5_evidence']:
  if ':' not in ev:continue
  k,path=ev.split(':',1)
  if k not in pins or not path.startswith(('docs/','design/','evidence/')):continue
  path=path.split('#')[0];text=read(k,path)
  evidence_audit.append(dict(id=r['id'],ref=k,path=path,found=text is not None))
(P/'evidence-audit5.json').write_text(json.dumps(evidence_audit,indent=2)+'\n')
counts=dict(rows=len(rows),classes=dict(collections.Counter(r['recount5_class'] for r in rows)),statuses=dict(collections.Counter(r['recount5_status'] for r in rows)),open_dependencies=dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount5_status']=='OPEN')),closure_routes=dict(collections.Counter(r['closure_route'] for r in rows if r['recount5_status']=='CLOSED-ON-CANDIDATE')),candidate_closure_imports=dict(collections.Counter(r['in_headline_closure5'] for r in rows if r['recount5_status']=='CLOSED-ON-CANDIDATE')),all_row_imports=dict(collections.Counter(r['in_headline_closure5'] for r in rows)),premises_removed_added_weakened=[0,0,0])
for n,x in [('rows5.json',rows),('totals5.json',counts),('manifest.json',manifest),('import-closures5.json',closures),('used-sources5.json',sorted(used))]:(P/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
lines=['# Recount 5 2026-10-27 (B)','','All 407 rows re-derived from pinned git objects; historical fields preserved. Import membership is not discharge. P6 bounds/carriers retained. N7 is custody, not a privacy-witness row. See recount5/METHOD5.md, pins.json, definition-audit5.json and rows5.json. Target not yet established.','','| Row / class 4 → 5 / name | Status 4 → 5 | OPEN bucket | in headline closure? | Derivation, retained obligation and evidence |','|---|---|---|---|---|']
for r in rows:
 status=r['recount5_status']+(' ('+r['closure_route']+')' if r['recount5_status']=='CLOSED-ON-CANDIDATE' else '')
 detail=r['recount5_basis']+' Residual: '+'; '.join(r.get('residual_fields',[]))+'. Evidence: '+'; '.join(r['recount5_evidence'])+'. Full witnesses: recount5/rows5.json#'+r['id']
 lines.append('|'+r['id']+' / '+r['recount4_class']+' → '+r['recount5_class']+' / '+r['name'].replace('|','\\|')+'|'+r['recount4_status']+' → '+status+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure5']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(B/'ROWS5.md').write_text('\n'.join(lines)+'\n');print(json.dumps(counts,indent=2))
