from auditlib7 import *
rows=json.loads((B/'recount6/rows6.json').read_text());by={r['id']:r for r in rows}
audit={a['id']:a for a in json.loads((P/'definition-audit7.json').read_text())}
for r in rows:
 a=audit[r['id']];r['recount6_closure_theorem']=r.get('closure_theorem');r['recount6_closure_route']=r.get('closure_route');r['recount6_bucket']=r['dependency_bucket'];r['recount7_status']=r['recount6_status'];r['recount7_class']=r['recount6_class'];r['definition_witnesses7']=a['sources'];r['definition_changed7']=a['changed_from6'];r['recount7_evidence']=['definition-audit7.json#'+r['id'],'../recount6/rows6.json#'+r['id']]
 r['recount7_basis']='Exact pinned defining statements/guards and supporting source bytes inspected; prior scoped derivation retained. '+r.get('meaning',r['name'])+'. '+r.get('rationale',r['recount6_basis'])
 r['residual7']='Prior quantified/model/native/deployment residual retained at recount6/rows6.json#'+r['id']
 if a['changed_from6']:r['recount7_basis']+=' Changed defining file is historical LOG reporting, not a changed formal statement; D301–D356 dispositions are in CORRECTIONS7.md.'
 # Re-read closing laws as full source statements, not labels; keep original sources.
 th=r.get('closure_theorem') if r['recount6_status']=='CLOSED-ON-CANDIDATE' else r.get('theorem','').split(' + ')[0] if r['recount6_status']=='CLOSED-ON-RESEARCH' else None
 if th:
  m=r.get('closure_source_module6') or ('.'.join(th.split('.')[:2]) if th.startswith(('R1Z.','R0Z.')) else th.split('.')[0]);found=[]
  for k in ['research','rw','cb','cb3','cblib','join']:
   s,path=module(k,m)
   if s and th.split('.')[-1] in s:found.append(dict(ref=k,path=path,sha256=hashlib.sha256(s.encode()).hexdigest()))
  assert found,(r['id'],th,m)
  r['closure_statements7']=found

def update(id,why,ev=(),status=None,route=None,theorem=None,source=None,residual=None):
 r=by[id];r['recount7_basis']=why;r['recount7_evidence']+=list(ev)
 if status:r['recount7_status']=status
 if route:r['closure_route']=route
 if theorem:r['closure_theorem']=theorem
 if source:r['closure_source_module7']=source
 if residual:r['residual7']=residual

new={
'V230':('PV_B3_Close134','source','Exact original callback carrier with explicit op8 concrete error type; no source-law hypothesis. Complete Result returns the 64-mask array; all 261 other callbacks and 27 other type fields framed. Symbolic nonvacuity supplies length64. Structural gate checks all136 ordered endpoint pairs, literal table and error order; OR idempotence/commutativity/associativity justify sort/dedup omission. Same-input native original/copy/emission comparisons are finite validation.'),
'V239':('PV_B3_Install222','source','Every representable raw QM31 column Slice and 10-coordinate point; no canonicality/success/source-law premise. Complete Result/Option with lossless four-limb carrier maps. Empty-column witness returns ok none, separately from the nonempty native/emission constant-seven fixture returning Some[7,0,0,0]. Structural correspondence preserves ordered field calls, reverse Boolean-suffix scan, populated-prefix storage and fold; unused initialized storage is not read. Finite native witness is not an unbounded native theorem.'),
'V217':('PV_B3_Install117','source','Every raw original QM31 16-coefficient/10-linear array, raw explicit value and10-point input. Complete Result law and lossless four-limb/array transports retain fail/div. No canonicality/success/source-law hypothesis. Successful all-zero witness is symbolic. Structural binding preserves coefficient tables,16/10 scatters,26 descending Horner steps, exact prepared helper calls and raw overflow semantics; raw-limb native comparisons are finite validation.'),
'V220':('PV_B3_Install121','source','Every raw original QM31 28-coefficient polynomial and challenge. Complete Result equals the exact grouped block evaluator, not a replacement naive Horner law; no canonicality/success/source-law premise. Nonvacuity is zero polynomial/challenge. Structural binding checks lifted captures,3x3 channels,arity-three aggregation and ordered prepared field calls with raw overflow retained. Native comparisons are finite validation.'),
'V256':('R1Z.PV_B2_F_AuditClosure','closed_rows','All byte slices, complete gamma sampler Result, mapped to the exact native carrier; no canonicality/success/source-law assumption. copy_equal_original and gamma_law identify the structural original representation. Nonvacuity is arbitrary-byte sampler success in the combined supplied-resource dictionary. Native4402-input comparisons are finite validation, not universal machine adequacy.'),
'V257':('R1Z.PV_B2_F_AuditClosure','closed_rows','All byte slices, complete ordinary sampler Result and exact native carrier; no canonicality/success/source-law assumption. copy_equal_original and selected value law identify the structural original representation. Nonvacuity is arbitrary-byte sampler success in the same combined dictionary. Native4402-input comparisons are finite validation.'),
'V258':('R1Z.PV_B2_F_AuditClosure','closed_rows','Every original weights/raw kappa and every input-dependent HeapRequest W→Native→Result Outcome. Complete materialization Result includes supplied/denied/fail/div and agrees before/after request sequencing. The theorem quantifies resource contexts; it does not prove their OS interpretation or witness independence. Native-carrier installation has no source-law premise. Supplied-success resources give nonvacuity shared with constructor/raw. Structural caller/allocation binding plus changed-write finite native/emission validation; not fresh extraction of original mutable iterator.'),
'V259':('R1Z.PV_B2_F_AuditClosure','closed_rows','Every native variant, raw10-coefficient alpha and2-point z; every input-dependent BoxRequest. Complete constructor Result agrees for all request outcomes, no success/canonicality/source-law premise. Constructor value nonvacuity constructs a weight shared with op251/op253 when resources succeed. Frozen fixed-row/caller-Box structural association, compiled layout assertion and finite allocation/drop/value witnesses. Retain the rejected boxed-allocation counterexample and authorized caller repair; actual allocator/world remains open.'),
'V260':('R1Z.PV_B2_F_AuditClosure','closed_rows','Every original weight, raw Usize kind and index, including invalid D indices, complete Result and exact native-carrier callback. valid_value_law retains its valid-input guards, while copy_equal_original/source and closed_rows are full-domain. Structural ordered-fold/table/guard binding preserves original arrayOutOfBounds before inactive checks; no success-only narrowing. Combined constructor supplies a successful kind0/index0 witness. Finite native values/errors are supporting validation; retained old assertionFailure counterexample is superseded by the authorized exact table repair.')}
verdicts=[]
for id,(m,th,why) in new.items():
 s,path=module('rw',m);assert s and re.search(r'theorem\s+'+th+r'\b',s),(id,path)
 law=(m.removeprefix('R1Z.') if m.startswith('R1Z.PV_B2_') else m)+'.'+th
 res='Native executable/caller/RunJoin V165/V167, deployed source/artifact association and L1/L2/L3 remain. D234/V403 mathematical reached-input interpretation remains where relevant; actual resource failure and witness independence are not discharged.'
 update(id,'CONFIRM CLOSED-ON-CANDIDATE at the selected source/callback boundary. '+why,ev=['rw:'+path,'closure-audit7.json#'+id],status='CLOSED-ON-CANDIDATE',route='structural source',theorem=law,source=m,residual=res)
 verdicts.append(dict(id=id,verdict='CONFIRM',theorem=law,source=path,full_statement_sources='closing-statements7.json',hypotheses_and_nonvacuity=why,native_evidence_class='structural source',residual=res,endpoint_premises_removed=0))
for id in ['V178','V179','V182','V195','V233']:
 path='evidence/pv-relink-20261028/'+id+'/row.json';v=json.loads(read('rw',path));binding='evidence/pv-relink-20261028/'+id+'-binding.json';b=json.loads(read('rw',binding))
 for c in b['checks']:
  if 'complete_body_tokens_match' in c:assert c['complete_body_tokens_match']
 update(id,'CONFIRM prior selected closure via structural (K-1 substitute). Historical reached-copy Kani PASS native link is SUSPENDED under (r), never re-credited by finite validation. Independent script-checked complete-body binding, listed Lean transports and complete-Result law plus '+v['finite_validation']+'. '+v['after']['residual'],route='structural (K-1 substitute)',ev=['rw:'+path,'rw:'+binding,'rw:evidence/pv-relink-20261028/REPORT.md','kstub:evidence/pv-kstub-20261028/README.md'],residual=v['after']['residual'])
 by[id]['kani_status7']='SUSPENDED historical copy-dependent PASS; exact KMX positive/control re-verification incomplete at pinned kstub head';by[id]['structural_relink7']=v
 verdicts.append(dict(id=id,verdict='CONFIRM structural replacement; historical Kani SUSPENDED',native_evidence_class='structural (K-1 substitute)',before_after=v,binding=binding,endpoint_premises_removed=0))
update('V184','CONFIRM standing structural stdlib complete-Result proof on arbitrary non-Copy payloads, representable Buffer, world/history/frame and zero/nonzero widths. K-1 suspends the reached-copy bounded Kani corroboration, not the independent pinned pop/remove/try_remove structural route and Lean move-world law. Retain copying-reference world mismatch as rejected; finite99 ordinary and33 Drop/ZST native cases do not prove universal allocator/compiler adequacy.',route='structural stdlib',ev=['rw:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_AL_MoveClosure.lean','research:evidence/pv-kscan-20261028/ROWS.md'])
by['V184']['kani_status7']='SUSPENDED supporting copy-exposed Kani gate; structural closure STANDS'
verdicts.append(dict(id='V184',verdict='CONFIRM structural closure STANDS; Kani support suspended',native_evidence_class='structural stdlib',endpoint_premises_removed=0))
for id,field in [('V152','public_eq'),('V153','build_eq'),('V154','transport_eq')]:
 update(id,'Raw-family row text retained: all w:source.Instance in SourceIdentification. The raw/admission-only identification conjunction is identification_unsatisfiable because an admitted cached semantic trace has1 at(0,13), while every canonical target has0 there. This is not a claim that each individual field is false: public projection can hold, a record-preserving canonical map need not exist on nonconserving inputs, and raw transport_eq holds. DISCHARGED at source_honest/target on Honest={i//HonestInput i} by PV_RunJoin_HonestIdentification26.'+field+'. HonestInput carries Admission, full run=ok(.Ok cached payload), Checked and canonical frontier. Generic consumers unchanged; both fixtures inhabit this family. Successful canonical preparation implies HonestInput remains OPEN, with zero-change rejection for both spend kinds and the raw noncanonical-frontier finding retained. No endpoint conjunct/RunJoin field is removed.',ev=['runjoin:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_HonestIdentification26.lean','runjoin:evidence/pv-runjoin24-20261027/REPORT.md','runjoin:evidence/pv-runjoin26-20261027/REPORT.md','runjoin:evidence/pv-runjoin31-20261028/recovery/RESUME32.md'],residual='Unconditional successful canonical preparation→HonestInput and complete native observable RunJoin V038/V045 remain; raw-family identification cannot be supplied.')
 by[id]['raw_family_classification7']='identification_unsatisfiable (conjunction; build_eq obstruction)';by[id]['honest_family_classification7']='discharged at honest family';by[id]['ledger_row_scope7']='original raw-family universal handoff; distinct honest-family instantiation recorded, not substituted'
for id in ['V038','V045','V047']:
 update(id,'Runjoin26 closes the honest-family initial builder/public/transport handoff and original-fixture Association/nonvacuity. It removes no RustRealRefinement conjunct or RunJoin field. V038 still requires complete ROMView plus observer decision equality on every common sample outside the fixed bad event with exact marginals. V045 retains native caller/body/world association; V047 fixtures do not witness arbitrary-x or full P∧T native-world satisfiability. Successful preparation→HonestInput remains open. D348 adds an explicit observer coverage gap, not an assumed log determinism theorem.',ev=['runjoin:evidence/pv-runjoin26-20261027/REPORT.md','D348.md'])
for id in ['V404','V405']:
 update(id,'OPEN a (prior bucket retained). Parked reach head ee0f9fb93c has installed-op84 noCatch and conditional source/client prefixes after dependency builds; dictionary congruence and poisoning do not prove complete invocation, exclusion, ordering or minimal reached sets. Native public/external/record associations are prerequisites; parked is not closed.',ev=['research:docs/research/v8-r0-zk-20261009/LOG.md#D335/D341'])
for id in ['V187','V201','V231','V234','V235','V236','V237','V238']:
 update(id,'OPEN d. Pinned dlib supplies supporting model/reference/selected constructor laws but no accepted native generic link at this head. Copy-dependent Kani constructor PASS1/2 are suspended under(r); rejected shipped wrapper extraction retained. Selected64 model witnesses and compression-parameter laws do not establish the generic native constructor/source association. Later dlib2 is not among the pinned branch results.',ev=['dlib:evidence/pv-dlib-20261028/V237/STATUS.md','research:docs/research/v8-r0-zk-20261009/LOG.md#D349'])
for id in ['V228','V229','V241','V243','V244','V245']:
 update(id,'OPEN at original bucket. Pinned b3p6 has supporting owned-reference/extraction/control/carrier laws and finite native validations. op133 target Kani gates, including exact KMX-patched runs, time out or remain unconfirmed; a failing growth control alone is not a positive gate. op226 serializer alternatives/partitioned emissions do not provide accepted original native link and selected row closure. No chained-field Kani route credited.',ev=['b3p6:evidence/pv-b3p6-20261028/JOURNAL.md'])
for id in ['V352','V354','V357','V360']:
 update(id,'OPEN at original bucket. Parked l2c local arithmetic/parser/fold/mask lemmas and128 changed-write native comparisons do not establish guard constancy on every honest input. No leak was found; no universal positive native link. Copy-dependent PASS suspended by K-1; final audit/replay missing project object and closure claim withdrawn (D355). l2c2 work is not silently included.',ev=['research:docs/research/v8-r0-zk-20261009/LOG.md#D355'])
update('V340','OPEN b. Fixed candidate6d4350e42c contains batch3 four structural closures, batch2 five and five K-1 structural substitutes, with no endpoint premise removal. Integ4/5 ELF,fixture and1000-pair differential evidence belongs to03905a5259, not later merges. D344 cumulative +1.59%/+1.71% cost is a projection. Pinned gate6 supplies fresh three matching ELF pins, pinned client and deterministic coin0 match on82566acdfb; fresh differential and quiet timing still pending in its committed snapshot. No measured final-candidate timing/adoption pass inferred.',ev=['gate6:evidence/pv-gate6-20261028/README.md','research:docs/research/v8-r0-zk-20261009/LOG.md#D328/D344/D350/D356'])
for id in ['V373','V374']:
 update(id,'OPEN c. Client toolchain already approved, features/CT decoding still owner decisions. Integ4 cost projections and uncoordinated samples are not qualified timing. Pinned gate6 full differential/timing is not complete in committed evidence; D356 live853/1000 progress is not final1000 or a timing pass. Nonconforming earlier dudect detection remains input-preparation artifact evidence, not a shipped leak/pass. L2 N2–N6 and physical DOITM transfer remain.',ev=['gate6:evidence/pv-gate6-20261028/README.md','research:docs/research/v8-r0-zk-20261009/LOG.md#D344/D356'])
update('V396','OPEN c. Client scope still devnet fixture harness versus wallet; caller-supplied Selection and public/compiled arguments need a concrete honest caller binding. Source identification is now proved for the explicit honest family, not arbitrary cached compilations. Canonical codec-first preparation→HonestInput remains open; zero change rejected for transfers/withdrawals. N7 is custody. D348 observer log/error coverage is a separate open owner matter.',ev=['runjoin:evidence/pv-runjoin26-20261027/REPORT.md','D348.md'])
# Per-row K-1 audit; STANDS never converts OPEN or REDUCED to closed.
s=read('research','evidence/pv-kscan-20261028/ROWS.md')
for r in rows:
 line=next((l for l in s.splitlines() if l.startswith('| '+r['id']+' |')),None);assert line,r['id'];r['k1_scan7']=line
 if r['recount7_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in 'abcd'
(P/'closure-audit7.json').write_text(json.dumps(verdicts,indent=2)+'\n')
# Same actual roots as recount6; do not add publication roots as consumers.
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
 ws=[];th=r.get('closure_theorem') if r['recount7_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  m=r.get('closure_source_module7') or r.get('closure_source_module6') or ('.'.join(th.split('.')[:2]) if th.startswith('R1Z.') else th.split('.')[0]);canonical=None
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
 r['in_headline_closure7']='research' if any(x['ref']=='research' for x in ws) else 'candidate' if ws else 'neither';r['import_witnesses7']=ws
 if r['recount7_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in 'abcd'
(P/'import-closures7.json').write_text(json.dumps(closures,indent=2)+'\n')
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(P/'rows7.json').write_text(json.dumps(rows,indent=2)+'\n')
t=dict(rows=len(rows),classes=dict(collections.Counter(r['recount7_class'] for r in rows)),statuses=dict(collections.Counter(r['recount7_status'] for r in rows)),open_dependencies=dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount7_status']=='OPEN')),closure_routes=dict(collections.Counter(r.get('closure_route') for r in rows if r['recount7_status']=='CLOSED-ON-CANDIDATE')),all_row_imports=dict(collections.Counter(r['in_headline_closure7'] for r in rows)),candidate_closure_imports=dict(collections.Counter(r['in_headline_closure7'] for r in rows if r['recount7_status']=='CLOSED-ON-CANDIDATE')),premises_removed_added_weakened=[0,0,0],raw_family_identification='unsatisfiable',honest_family_identification='discharged',observer_logs_errors='coverage gap')
(P/'totals7.json').write_text(json.dumps(t,indent=2)+'\n')
lines=['# Recount 7 2026-10-28 (B)','','Every row re-derived by METHOD7 at immutable pins. Historical fields and exact scopes retained. Source/native classes and hypotheses/nonvacuity are in recount7/closure-audit7.json; all full source witnesses in manifest.json. Raw-family identification and honest-family discharge are separate facts. Target not yet established.','','| Row / class6 →7 / name | Status6 →7 | OPEN bucket | in headline closure? | Derivation, residual and evidence |','|---|---|---|---|---|']
for r in rows:
 detail=r['recount7_basis']+' Residual: '+r['residual7']+'. Full witnesses: recount7/rows7.json#'+r['id']
 lines.append('|'+r['id']+' / '+r['recount6_class']+' → '+r['recount7_class']+' / '+r['name'].replace('|','\\|')+'|'+r['recount6_status']+' → '+r['recount7_status']+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure7']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(B/'ROWS7.md').write_text('\n'.join(lines)+'\n');print(json.dumps(t,indent=2))
