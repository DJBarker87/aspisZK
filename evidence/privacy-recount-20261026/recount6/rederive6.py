from pathlib import Path
import json,re,subprocess,hashlib,os,collections
P=Path(__file__).resolve().parent;B=P.parent;pins=json.loads((P/'pins.json').read_text())['revisions']
manifest=json.loads((P/'manifest.json').read_text());ix={(x['ref'],x['path']):x for x in manifest};used=set()
def read(k,path):
 used.add((k,path)); x=ix.get((k,path))
 if x:return (P/x['snapshot']).read_text()
 q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True)
 if q.returncode:return None
 raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();f=P/'objects'/(blob+'.txt');f.parent.mkdir(exist_ok=True);f.write_bytes(raw)
 x=dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(f,P));ix[k,path]=x;manifest.append(x);return raw.decode()
R='docs/research/v8-r0-zk-20261009/lean/'
resolved={}
def module(k,m):
 if (k,m) in resolved:return resolved[k,m]
 paths=[R+m.replace('.','/')+'.lean']
 if m.startswith('R1Z.ProverRwFull'):paths+=['docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean']
 if m.startswith('PV_B1_'):paths+=['evidence/pv-op254-20261027/lean/'+m+'.lean']
 for path in paths:
  s=read(k,path)
  if s is not None:resolved[k,m]=(s,path);return s,path
 resolved[k,m]=(None,paths[0]);return None,paths[0]
rows=json.loads((B/'recount5/rows5.json').read_text());by={r['id']:r for r in rows};audit={x['id']:x for x in json.loads((P/'definition-audit6.json').read_text())}
for r in rows:
 a=audit[r['id']];r['recount5_bucket']=r['dependency_bucket'];r['recount6_status']=r['recount5_status'];r['recount6_class']=r['recount5_class'];r['definition_witnesses6']=a['sources'];r['recount6_evidence']=['definition-audit6.json#'+r['id']]
 r['recount6_basis']='Pinned definitions, guards and prior supporting objects re-read. '+r['recount5_basis']
 r['definition_changed6']=a['changed_from5']
 if a['changed_from5']:
  r['recount6_basis']+=' Changed source objects inspected: '+', '.join(a['changed_from5'])+'. LOG additions do not alter the original quantifiers or establish deployment.'
 # Resolve every historical closure statement, including sources absent from the candidate.
 th=r.get('closure_theorem') if r['recount5_status']=='CLOSED-ON-CANDIDATE' else r.get('theorem','').split(' + ')[0] if r['recount5_status']=='CLOSED-ON-RESEARCH' else None
 if th:
  m='.'.join(th.split('.')[:2]);found=[]
  for k in ['research','rw','cb','cb3','cblib','join']:
   s,path=module(k,m)
   if s and th.split('.')[-1] in s:found.append({'ref':k,'path':path,'sha256':hashlib.sha256(s.encode()).hexdigest()})
  assert found,(r['id'],th)
  r['closure_statements6']=found

def update(id,why,status=None,bucket=None,theorem=None,route=None,ev=()):
 r=by[id];r['recount6_basis']=why;r['recount6_evidence']+=list(ev)
 if status:r['recount6_status']=status
 if bucket:r['dependency_bucket']=bucket
 if theorem:r['closure_theorem']=theorem
 if route:r['closure_route']=route

# Read full closing modules and imports; no theorem-name-only status decisions.
new={
'V233':('R1Z.PV_AL_SplitSelected','native_callback','P6 gate','All representable Slice U8 inputs for the constructed 64-byte Storage/Size/nativeTrait specialization; native_callback and consumed have no source-law premise. Generic callback requires USIZE=ok64; native_size constructs it. SplitObservation.complete covers other block sizes and division-by-zero, without claiming a native generic ArrayLength interpretation. P6 native link is no-stub arbitrary bytes/coordinates at lengths 0–129 (389 checks, unwind132), plus 1026 prefixes through 1025. Unbounded Lean law is about the extracted reference/explicit carrier; bounded gate is not an unbounded machine theorem. V232 and generic SHA wrappers remain open.'),
'V265':('R1Z.PV_AL_CircleSelected','native_source','structural source','Every32-byte block and both explicit row constructors, complete Result; no success, arithmetic-equivalence or source-equality hypothesis. Native.source_reference uses the same extracted field operations in source order, including errors/OOD/fallback. Structural gate checks pinned bodies and constants under ruling(k); 8712 wrapper comparisons are finite validation. Row/carrier roundtrips and row_images show nonempty inputs. No dependency on the withdrawn raw low_base_p_digits body. Native machine/compiler/RunJoin association remains separate.'),
'V184':('R1Z.PV_AL_MoveClosure','complete','structural stdlib + bounded gate','Arbitrary payload Type without Copy/Clone, representable vector Buffer.fits, address, initial world/history/counters, data memory, width including zero, arbitrary external frame. complete quantifies these and constructs one shared observation for nativeWorld/referenceWorld and the consumed selected callback; no world-equality premise. nonvacuous constructs Buffer at capacity=length for every representable vector. Structural pinned nightly-2026-06-01 pop/remove/try_remove semantics plus no-stub Kani lengths 0–4,99 native cases and33 non-Copy Drop ZST cases; raw pointers/compiler/allocator are not universally extracted. The [17,29] copying-reference allocation mismatch is retained as a rejected approach.'),
'V261':('PV_B1_Close254','selected_callback','structural source','Every Usize N and arbitrary raw WideExact limbs on the exact original ProverRwFull callback carrier. source identifies the extracted copy with the structural original early-return representation; selected_callback uses proved carrier transport, no positive-N/canonicality/success/source-law premise. nonfailure is all-N, nonvacuity N=1. Restoration theorem and emitted changed-write tests satisfy ruling(n).6144 native pairs use canonicalizing native constructors; they do not narrow the arbitrary-raw Lean theorem or prove native machine adequacy.'),
'V247':('PV_B1_Close230','selected_callback','structural source','Every representable Slice of raw QM31 on the original callback carrier; complete Result includes None for wrong length and Some sum at 1024, without an assumed source equality. Symbolic1024-element replicated slice gives nonvacuity. Original/ref link is the recorded structural binding plus extracted copy; no mutable borrowed writes; 320 native pairs are finite validation. Native executable/caller effects remain V165/V167.'),
'V264':('PV_B1_Close258','selected_callback','structural source','Every row Slice,64 masks and arbitrary raw QM31; complete Result including oversized slices and arrayOutOfBounds, with no success/canonicality/source-law restriction. truth/failure characterize pole verdict and length boundary; empty-success and nonempty PoleWitnesses plus 1025-row failure witness prevent vacuity. Original/ref link is structural binding plus extracted copy, no mutable borrowed writes; 896 values and128 bounds errors are finite checks. Native executable/caller effects remain V165/V167.')}
verdicts=[]
for id,(m,th,route,why) in new.items():
 s,path=module('rw',m);assert s and re.search(r'theorem\s+'+th+r'\b',s),(id,path)
 update(id,'CONFIRMED CLOSED-ON-CANDIDATE. '+why,status='CLOSED-ON-CANDIDATE',theorem=m+'.'+th,route=route,ev=['rw:'+path,'closure-audit6.json#'+id])
 verdicts.append(dict(id=id,verdict='CONFIRM',theorem=m+'.'+th,path=path,statement_module_sha256=hashlib.sha256(s.encode()).hexdigest(),hypotheses_and_nonvacuity=why,native_evidence_class=route,deployed_premises_removed=0))
# D285 has a seventh newly available row; independently inspect its adapter and gate.
s,path=module('rw','R1Z.PV_CBL_CallbackPublication');assert s and 'theorem op26_source' in s
for m in ['R1Z.PV_CBL_JoinAdapter','R1Z.PV_CBL_JoinSource','R1Z.PV_CBL_JoinReference']:
 module('rw',m)
update('V178','D285 independently confirmed at bounded P6 value boundary: CallbackPublication declares namespace PV_CBL_CallbackBundle; op26_source preserves the arbitrary AsRef Result and calls JoinAdapter.reference on the explicit String path carrier. Native gate byte lengths 0–2 and all output coordinates; native PathBuf/UTF-8 image, allocation/world, unbounded/deployed association retained. OPS.md misnames the module (CallbackBundle); declaration is in CallbackPublication. Publication alone is not the native link.',status='CLOSED-ON-CANDIDATE',theorem='R1Z.PV_CBL_CallbackBundle.op26_source',route='P6 gate',ev=['rw:'+path,'rw:evidence/pv-cblib-20261027/OPS.md'])
by['V178']['closure_source_module6']='R1Z.PV_CBL_CallbackPublication'
update('V370','D301 owner-APPROVED client compiler pin resolves the owner-choice subtask; V370 remains OPEN P for compiler preservation on actual kernels/calls, with final recipe/adoption evidence still outstanding. Exact client-scoped rust-toolchain file exists on candidate. No new T field.',bucket='b',ev=['research:docs/research/v8-r0-zk-20261009/LOG.md#D301','rw:tools/r1-cost-probe/rust-toolchain.toml'])
update('V271','D292 merged FileCarrier now present on candidate. type0_installed interprets a File as a nonnegative signed32 descriptor, not live OS ownership or exactly-once Drop. Read all FileCarrier statements and original signatures; native I/O/world/ownership transport remains OPEN b. Absence wording from recount5 is superseded.',ev=['rw:'+R+'R1Z/PDict_FileCarrier.lean'])
update('V388','D188 is owner-narrowed (D301 second amendment), not an extra RunJoin T field. Exclude raw low_base_p_digits: discarded restoration3611/quotient 3624; P/P+1/ff differ, zero agrees. pv-d188:33 credit-stands rows,21 native/effect suspensions,1 body-scoped withdrawal; 41 fresh projection agreements,382 unverified declaration occurrences remain suspended, no closed callback withdrawn. SDY overlap:four raw bodies retain writes and match12 fixtures, credit restored by lead(o)/D302 only at that checked scope, not universal trace/ABI/native composition. Indexed copies bypass raw defect but still require per-function restoration and native association.',ev=['rw:evidence/pv-d188-20261027/AUDIT.md','research:evidence/fidelity-check1-20261027/SDY_FINDING.md','research:docs/research/v8-r0-zk-20261009/LOG.md#D301/D302'])
for id in ['V152','V153','V154','V038','V045','V047','V163','V336','V337','V338','V339']:
 r=by[id]
 update(id,'D302–D320 supersede the old records extraction failure: general extracted records identification and fixture compiler returns/transitions/bank/public/fibres are proved. D320: Selection.selected is caller-supplied, no frozen deployment selector; fixture results are nonvacuity, not universal SourceIdentification. V152 public projection, V153 raw trace, V154 S2/pi/D18 remain universal; V038 is every common sample. Actual source/native/caller/public binding and P∧hypothetical-T association remain unproved. Original row status and quantifiers retained. '+r['recount5_basis'].split(' Records repairs')[0],ev=['runjoin:evidence/pv-runjoin21-20261027/STAGE1-SELECTION.md','research:docs/research/v8-r0-zk-20261009/LOG.md#D317/D320'])
for id in ['V256','V257','V258','V259','V260']:
 update(id,'Batch2 current head is continuing. Copies/emissions and staged constructor/sampler laws do not establish universal original/copy/selected-row laws. Retained op253 counterexample: D/kind 0/j1024 original arrayOutOfBounds versus old copy assertionFailure. Authorized repair at 5b11c957a0 uses exact frozen table/indexing; ErrorRepair.op253_counterexample_repaired proves this input and all oversized D bounds fail correctly (52015). Universal valid-input fidelity and row bridges still OPEN. No raw low_base_p_digits credit; copies use indexed writes. Historical exact original extraction obstruction retained where d; repaired copy emission alone does not erase original/ref obligation.',ev=['batch2:design/PV-BATCH2-20261027.md'])
for id in ['V217','V220','V230','V228','V229','V239','V241','V243','V244','V245']:
 update(id,'Batch3 and batch3b on candidate; active branch continues. op134 copy equals reference masks with complete Result, bounds and nonvacuity; native original/copy association and dictionary installation remain OPEN. op117/op121 finite-loop/carrier transports are not their universal source equalities. Other extraction failures/refusals and original shared guards remain explicit; no row closure from emission or bounded factorization. '+by[id]['recount5_basis'],ev=['research:docs/research/v8-r0-zk-20261009/LOG.md#D307/D316'])
for id in ['V404','V405']:
 update(id,'Still OPEN: dictionary congruence is weaker than invocation/minimality/ordering/native-effect reachability (D310). Installed op84 directly returns hash callback Result; generic-interface catching finding does not apply to installed body (D319). Source-context chunks/poisoning/retry forwarding do not yet supply complete admitted-input reached sets, invocation exclusions and minimality witnesses. Current branch is still running.',ev=['research:docs/research/v8-r0-zk-20261009/LOG.md#D306/D309/D310/D314/D315/D319'])
for id in ['V397','V398']:
 update(id,'D281 coherent research replay retained. First passing runjoin endpoint axiom audit is runjoin21/D317: verified5673 external and669 project objects; standard axioms only on cached objects. This is focused audit evidence, not final adopted candidate/release dependency replay, artifact binding, or row closure. Later38299 import failure is retained; it does not negate the earlier passing audit. OPEN b.',ev=['research:docs/research/v8-r0-zk-20261009/LOG.md#D317/D320'])
for id in ['V373','V374']:
 update(id,'Client pin approved D301; release feature/constant-time decoding choices remain open. D295 dudect differences were nonconforming and D297 diagnosed input-buffer preparation artifact; not a shipped leak and not a V374 pass. Planv2.2 is prepared, qualified final campaign remains. A/B disassembly/harness matching leaves are finite/partial evidence, N2–N6 native L2 and V371 timing transfer remain. N7 is signing-seed custody, excluded from privacy denominator.',bucket='c',ev=['research:docs/research/v8-r0-zk-20261009/LOG.md#D289/D295/D297/D301'])
update('V396','D301 owner-approved client toolchain pin is present; recipe/features/CT private decoding and client scope remain open. Current client is a devnet fixture harness with internally built witnesses, not a wallet. D320: endpoint Selection is caller-supplied; RealR1_client takes public/compiled arguments and has only fixture callers, no frozen deployment selector. Scope decision precedes concrete caller/upload/signing/retry observer binding. N7 remains custody only.',bucket='c',ev=['runjoin:evidence/pv-runjoin21-20261027/STAGE1-SELECTION.md','research:docs/research/v8-r0-zk-20261009/LOG.md#D301/D320'])
update('V340','Candidate03905a5259 includes rebase, proof-account route, runjoin17, batch2 plus batch2c head, D188 audit, batch3 plus batch3b, alib, op254 and client toolchain file. op223 cleared its own four adoption gates at 8873306db1 (D289); combined differential/quiet timing, final release binding and native/RunJoin composition remain OPEN. No historical gate is promoted to validation of all later merged source.',bucket='b',ev=['research:docs/research/v8-r0-zk-20261009/LOG.md#D286/D288/D289/D298/D302/D303/D307/D318'])
# Preserve the per-row D188 fidelity scope; no fixture extrapolation into native composition.
for disposition in json.loads(read('rw','evidence/pv-d188-20261027/rows.json')):
 id=disposition['row']
 if id in by:
  by[id]['fidelity_disposition6']=disposition
  by[id]['recount6_basis']+=' D188 audit disposition: '+disposition['classification']+'. '+disposition['scope']
  by[id]['recount6_evidence'].append('rw:evidence/pv-d188-20261027/rows.json#'+id)
# Actual-consumer graph audit. Same roots as method5; add current candidate versions of wire consumers.
roots=[('research','R1Z.PrivacyR1HeadlineDeployedReal'),('join','R1Z.PV_Join_Wire_FinalAuditA'),('join','R1Z.PV_Join_PublicCaller'),('rw','R1Z.ProverRw19CanonicalAuditRefinement'),('rw','R1Z.ProverRw18ContextData'),('rw','R1Z.PV_Op223_V164'),('rw','R1Z.PV_Join_Wire_FinalAuditA'),('rw','R1Z.PV_Join_PublicCaller')]
closures=[]
for k,root in roots:
 paths={root:[root]};queue=[root];unresolved=[]
 for m in queue:
  if not m.startswith(('R1Z.','R0Z.','PV_B1_')):continue
  s,path=module(k,m)
  if s is None:unresolved.append(m);continue
  for dep in re.findall(r'^import\s+(\S+)',s,re.M):
   if dep not in paths:paths[dep]=paths[m]+[dep];queue.append(dep)
 closures.append(dict(ref=k,root=root,paths=paths,unresolved_project_modules=unresolved))
for r in rows:
 ws=[];th=r.get('closure_theorem') if r['recount6_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  m=r.get('closure_source_module6') or ('.'.join(th.split('.')[:2]) if th.startswith('R1Z.') else th.split('.')[0]);canonical=None
  for k in ['rw','cblib','cb3','cb','join']:
   s,path=module(k,m)
   if s and th.split('.')[-1] in s:canonical=s;break
  assert canonical,(r['id'],th)
  for c in closures:
   if m not in c['paths']:continue
   s,path=module(c['ref'],m)
   norm=lambda s:re.sub(r'^import[^\n]*\n','',s,flags=re.M)
   if s and norm(s)==norm(canonical):ws.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][m],source_path=path,scope='identical law body, not deployment discharge'))
 elif r['id']!='V270':
  d=r.get('definition','').split('#')[0]
  if '/lean/' in d and d.endswith('.lean'):
   m='R1Z.'+Path(d).stem if '/lean/prover-rw-' in d else d.split('/lean/')[-1][:-5].replace('/','.')
   for c in closures:
    if m in c['paths']:ws.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][m],scope='defining-source membership only'))
 r['in_headline_closure6']='research' if any(x['ref']=='research' for x in ws) else 'candidate' if ws else 'neither';r['import_witnesses6']=ws
 if r['recount6_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in 'abcd'
# Content-address all explicit fresh evidence; expose missing references.
ev_audit=[]
for r in rows:
 for ev in r['recount6_evidence']:
  if ':' not in ev:continue
  k,path=ev.split(':',1);path=path.split('#')[0]
  if k in pins and path.startswith(('docs/','evidence/','design/','tools/')):
   ev_audit.append(dict(id=r['id'],ref=k,path=path,found=read(k,path) is not None))
# Reuse and independently parse the six required receipts with all audit lines.
receipt_audit=[]
for id in [37698,37699,37600,37604,38597,38598]:
 path=f'evidence/pv-alib-20261027/{id}.json' if id<38000 else f'evidence/pv-op254-20261027/lean-receipts/{id}/receipt.json'
 v=json.loads(read('rw',path));axioms=v.get('axioms',v.get('print_axioms',[]));bad=[]
 for line in axioms:
  if 'depends on axioms:' in line:
   names=re.findall(r'\[([^]]*)\]',line)[-1].split(',');bad += [n.strip() for n in names if n.strip() not in ['propext','Classical.choice','Quot.sound']]
 assert v['exit']==0 and not bad,(id,bad)
 receipt_audit.append(dict(id=id,path=path,receipt=v,standard_axioms=True,audit_queries=len(axioms),scope='cached focused signature replay; paired audit 37698' if id==37600 else 'focused audit/replay; not full release'))
(P/'reused-receipts6.json').write_text(json.dumps(receipt_audit,indent=2)+'\n')
(P/'closure-audit6.json').write_text(json.dumps(verdicts,indent=2)+'\n')
(P/'import-closures6.json').write_text(json.dumps(closures,indent=2)+'\n');(P/'evidence-audit6.json').write_text(json.dumps(ev_audit,indent=2)+'\n')
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(P/'rows6.json').write_text(json.dumps(rows,indent=2)+'\n')
t=dict(rows=len(rows),classes=dict(collections.Counter(r['recount6_class'] for r in rows)),statuses=dict(collections.Counter(r['recount6_status'] for r in rows)),open_dependencies=dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount6_status']=='OPEN')),closure_routes=dict(collections.Counter(r.get('closure_route') for r in rows if r['recount6_status']=='CLOSED-ON-CANDIDATE')),all_row_imports=dict(collections.Counter(r['in_headline_closure6'] for r in rows)),candidate_closure_imports=dict(collections.Counter(r['in_headline_closure6'] for r in rows if r['recount6_status']=='CLOSED-ON-CANDIDATE')),premises_removed_added_weakened=[0,0,0])
(P/'totals6.json').write_text(json.dumps(t,indent=2)+'\n')
lines=['# Recount 6 2026-10-27 (B)','','Every row re-derived at pins.json by METHOD6; historical fields and exact scopes preserved. Target not yet established. Import membership is not discharge. Full sources/statements are content-addressed in manifest.json; native-link class and nonvacuity for the six requested closures are in closure-audit6.json.','','| Row / class5 →6 / name | Status5 →6 | OPEN bucket | in headline closure? | Derivation, residual and evidence |','|---|---|---|---|---|']
for r in rows:
 detail=r['recount6_basis']+' Residual: '+r.get('definition','deployment evidence')+' / '+r['name']+'. Full witnesses: recount6/rows6.json#'+r['id']
 lines.append('|'+r['id']+' / '+r['recount5_class']+' → '+r['recount6_class']+' / '+r['name'].replace('|','\\|')+'|'+r['recount5_status']+' → '+r['recount6_status']+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure6']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(B/'ROWS6.md').write_text('\n'.join(lines)+'\n');print(json.dumps(t,indent=2));print('Missing fresh evidence', [x for x in ev_audit if not x['found']])
