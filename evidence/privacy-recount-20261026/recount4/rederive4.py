from pathlib import Path
import json,re,subprocess,hashlib,collections
P=Path(__file__).resolve().parent; BASE=P.parent
pins=json.loads((P/'pins.json').read_text())['revisions']
manifest=json.loads((P/'manifest.json').read_text()); index={(x['ref'],x['path']):x for x in manifest};used=set()
def read(k,path):
 used.add((k,path))
 x=index.get((k,path))
 if x and (P/x['snapshot']).exists():return (P/x['snapshot']).read_text()
 q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True)
 if q.returncode:return None
 blob=subprocess.check_output(['git','rev-parse',pins[k]+':'+path],text=True).strip();out=P/'objects'/(blob+'.txt');out.write_bytes(q.stdout)
 x=dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(q.stdout).hexdigest(),snapshot=str(out.relative_to(P)));manifest.append(x);index[k,path]=x
 return q.stdout.decode()
R='docs/research/v8-r0-zk-20261009/lean/'
def module(k,m):
 path=R+m.replace('.','/')+'.lean';s=read(k,path)
 if s is None and m.startswith('R1Z.ProverRwFull'):
  path='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean';s=read(k,path)
 return s,path
rows=json.loads((BASE/'recount3/rows3.json').read_text());by={r['id']:r for r in rows}
audit=json.loads((P/'definition-audit4.json').read_text());ad={a['id']:a for a in audit}
oldad={a['id']:a for a in json.loads((BASE/'recount3/definition-audit3.json').read_text())}
for a in audit:
 old=oldad.get(a['id'],{}).get('sources',[]);oldsha={x['sha256'] for x in old}
 a['same_source_as_recount3']=[x['ref'] for x in a['sources'] if x['sha256'] in oldsha]
 a.pop('unchanged_research_definition',None)
for r in rows:
 r['recount4_status']=r['recount3_status'];r['recount4_class']=r['classification'];r['recount3_bucket']=r['dependency_bucket']
 r['recount4_basis']='Original scoped statement/guards re-read in the pinned definition objects. '+r['recount3_basis']
 r['recount4_evidence']=['definition-audit4.json#'+r['id'],'../recount3/rows3.json#'+r['id']]
 r['definition_witnesses']=ad[r['id']]['sources'];r['closure_route']='extraction' if r['recount3_status']=='CLOSED-ON-CANDIDATE' and r['id']!='V270' else 'axiom diagnostic' if r['id']=='V270' else None
 r['shared_obstruction']=None
 # Exact model-scope proof statements are re-read as well as the original structure definitions.
 if r['recount3_status']=='CLOSED-ON-RESEARCH':
  th=r.get('theorem','').split(' + ')[0];m='.'.join(th.split('.')[:2]);s,path=module('research',m)
  r['research_closure_statement']=dict(theorem=th,path=path,source_found=s is not None,sha256=hashlib.sha256(s.encode()).hexdigest() if s else None)
  assert s is not None,(r['id'],th)
  r['recount4_basis']='MODEL-scoped closure retained, with the original guards and quantifiers; no deployed/native instance inferred. '+r['recount3_basis']
 # Trust is capped to the adopted record, with the explicit V371 hardware exception.
 if r['classification']=='T' and r['id'] not in ['V329','V371']:
  r['recount4_class']='P'
  r['recount4_basis']='D248: '+('classical ROM experiment/model association is P, retaining the fixed ideal-oracle scope; no native SHA security theorem or fourth TrustItems field inferred. ' if r['id']=='V391' else 'not an additional accepted TrustItems field; concrete native/source association remains P. ')+r['meaning']+'. Original named interface remains unresolved; inherited REDUCED is not proof or adoption of a fourth T field.'
  r['recount4_evidence']+=['research:design/PRIVACY-LEDGER-20261026.md#Owner decisions 2026-10-27 (B)']
def change(id,status,why,bucket=None,route=None,th=None,ev=(),cls=None,fields=None):
 r=by[id];r['recount4_status']=status;r['recount4_basis']=why;r['dependency_bucket']=bucket if status=='OPEN' else None
 if cls:r['recount4_class']=cls
 if route:r['closure_route']=route
 if th:r['closure_theorem']=th
 r['recount4_evidence']+=list(ev)
 if fields is not None:r['residual_fields']=fields
# Re-derive all callback source rows from the exact operation-number table, not LOG labels.
cbtable=read('cb','evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md');cbids=[]
for line in cbtable.splitlines():
 if 'ROW-DISCHARGED(candidate)' not in line:continue
 c=line.split('|');op=int(c[1]);r=next(x for x in rows if x.get('group')=='O' and re.match(r'op'+str(op)+r'\b',x['name']))
 assert r['id']==c[2];th=c[4].strip();m='.'.join(th.split('.')[:2]);s,path=module('cb',m);assert s and re.search(r'(?:theorem|abbrev)\s+op'+str(op)+'_source',s)
 change(r['id'],'CLOSED-ON-CANDIDATE','Complete extracted-source Result law retained at the exact operation; arbitrary declared inputs, nominal conversions and failure/divergence unchanged. Native effects/carriers/release association remain V165–V167.',route='extraction',th=th,ev=['cb:evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md','cb:'+path]);cbids.append(r['id'])
assert len(cbids)==23
for op,id in [(120,'V219'),(225,'V242'),(246,'V254')]:
 m='R1Z.PV_CB3_Op'+str(op)+'Source';s,path=module('cb3',m);assert s and 'op'+str(op)+'_source' in s
 change(id,'CLOSED-ON-CANDIDATE','Complete extracted-source Result equation in the CB3 bundle; unrelated callbacks remain arbitrary. Source/native/release joins retained. Unique addition: op229/V246 is already in cb and is not counted a second time.',route='extraction',th=m+'.op'+str(op)+'_source',ev=['cb3:'+path])
change('V195','CLOSED-ON-CANDIDATE','cb5 repairs the old canonicalizing harness: arbitrary eight-u32 WideExact carriers, complete Result and a proved nominal carrier conversion. P6 native gate/structural fixed-width correspondence is now credited at candidate scope. The source theorem installs the extracted owned reference; it is not direct extraction of the shipped whole function. Native/deployed association remains.',route='P6 gate',th='R1Z.PV_CB3_Op51Arbitrary.op51_source',ev=['cb3:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB3_Op51Arbitrary.lean','LOG D236; cb5 RESUME_FINAL.json'])
for id,op in [('V177',25),('V180',29),('V185',34),('V186',35),('V179',28)]:
 why={25:'PathBuf deref',29:'PathBuf as_ref',34:'Vec::is_empty',35:'Vec::default',28:'String as_ref Path'}[op]
 bound='native arbitrary Unix byte paths length ≤4, arbitrary queried byte index; Path selectedTypes sets Path = retained opaque PathBuf; native layout/lifetime/world association not proved' if op in [25,29] else 'native Result<Word,Error> vectors length ≤2 (u8 gate ≤8); generic extracted length law; no unbounded native vector theorem inferred' if op==34 else 'loop-free empty Vec at actual Result<Word,Error> monomorphization; native length and capacity 0' if op==35 else 'native valid UTF-8 strings of exactly two bytes, arbitrary queried index; selectedString specializes String and Path/PathBuf carriers; no arbitrary-length native gate'
 change(id,'CLOSED-ON-CANDIDATE',why+': owned safe reference extracted and selected callback equation supplied; no-stub bounded Kani link. '+bound+'. Pure view/empty/default body is loop-free; the harness construction loops are bounded, so the native verdict itself remains bounded. Structural library source inspection supports the candidate route, never an extraction of the shipped std/alloc body. Separate extraction and Kani toolchains, and deployed association, retained.',route='P6 gate',th='R1Z.PV_CBL_CallbackBundle.op'+str(op)+'_source',ev=['cblib:evidence/pv-cblib-20261027/OPS.md','cblib:evidence/pv-cblib-20261027/RESUME.md','cblib:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CBL_CallbackBundle.lean'])
change('V240','CLOSED-ON-CANDIDATE','Applied prover-local index-loop compressor passes unchanged extractor; exact source selector and arbitrary-input complete-Result P6 bridge published. This is extraction of the applied candidate, not the unchanged shared verifier helper. Candidate adoption/three ELF pins/fixtures/1000-pair/timing and deployed identification remain independent gates. V164 uses the same law, not another callback decrement.',route='extraction',th='R1Z.PV_Op223_Source.op223_source',ev=['op223:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Op223_Source.lean','op223:evidence/pv-op223-20261027/OBLIGATIONS.md'])
change('V164','CLOSED-ON-CANDIDATE','Applied-candidate bridge supplies P_source_p6 from V240. BEFORE: ProverRw19CanonicalAuditRefinement.refinement takes P_source_p6, reservation and P_proof_bytes. AFTER: PV_Op223_V164.refinement specializes to PV_Op223_Source.selected ops and supplies P_source_p6; reservation and P_proof_bytes remain. Generic historical arbitrary dictionary and deployed privacy endpoint are unchanged. Count the bridge row once and the callback inventory decrement only at V240.',route='extraction bridge',th='R1Z.PV_Op223_V164.refinement',ev=['op223:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Op223_V164.lean','op223:evidence/pv-op223-20261027/OBLIGATIONS.md'])
change('V163','OPEN','rw21 publishes ProverRw21ModelInstance, a mathematical transcript serializer, not the deployed-input-to-Transcript construction or either fixture/general proof-byte equation. D245 missing identification: Records.call R_shipped w 600 (some recipient) change snapshot 77 = @PV_Src_RecordDynamic.call E_shipped w 600 (some recipient) change snapshot 77, on the identical deterministic witness/recipient/change/snapshot. R_shipped is absent: BuilderForestAdmissionPort Records remains opaque, source leaf sourceRecords.call. Downstream native run = ok (.Ok i.compiled), transition equality, model and full data association remain open. RunJoin12 publishes no such theorem.',bucket='b',ev=['rw:docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw21ModelInstance.lean','runjoin:evidence/pv-runjoin11-20261027/stage1-missing-fact.md','runjoin:evidence/pv-runjoin11-20261027/stage2-missing-fact.md','runjoin:evidence/pv-runjoin12-20261027/STATUS.md'])
for id in ['V152','V153','V154']:
 change(id,'REDUCED','Source-identification now merged on research with CLEAN (h\') merge gate: 1,028 project objects/zero gaps, 5,640 external links. The 21 source parent cells and publicCorr SOURCE root-helper equation are proved at explicit dictionary/E_shipped adapter. Deployed publicCorr snapshot/Records association remains REDUCED; words/admission/row_call REDUCED; compile_call OPEN. Deployed PV_Src_Premises remains five fields. No deployed source-identification closure is inferred.',ev=['research:evidence/pv-srcid3-20261026/MERGE-GATE.md','research:evidence/pv-srcid3-20261026/RESUME9-OBLIGATIONS.md','research:evidence/pv-srcid3-20261026/RESUME9-STAGES.md'],fields=['compile_call OPEN; D245 Records and installed compiler identification','words/admission/row_call REDUCED; publicCorr source half closed, deployed half REDUCED'])
for id in ['V038','V045','V336','V337','V338','V339']:
 change(id,'REDUCED','RunJoin8–12 constructed candidate P = {source public binding, trace}; initial/causal/identity/common_public checked at their candidate selection. Deployed P remains OPEN, record counts 2/8/6 unchanged; actual Runtime/Boundary, compiler records, native interpretation, complete trace and P∧T fixture non-vacuity are missing. D245 exact missing shipped Records identification is retained. T now adopted, capped to three fields, not deployed equality to the security experiment.',ev=['runjoin:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_TrustEndpoint.lean','runjoin:evidence/pv-runjoin11-20261027/stage2-missing-fact.md'])
change('V406','REDUCED','D248 owner adoption is DONE. The accepted aggregate T has exactly entropy_law, entropy_kernel, observation; capped. entropy_law overlaps V329 and is not a fourth field. Observation relates complete native/extracted outcomes and filesystem, not security-experiment agreement. Actual deployment Data and all ProofObligations stay P; adopting trust is not proving its native instance. No additional T field.',cls='T',ev=['research:design/PRIVACY-LEDGER-20261026.md#Owner decisions 2026-10-27 (B)','runjoin:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_TrustItems.lean'],fields=['accepted three-field T on actual deployment Data; no additional field; overlap V329'])
by['V329']['recount4_basis']='Adopted capped entropy_law field of PV_RunJoin_TrustItems; successful 64-byte conditional law, not OS availability. Overlaps V406 aggregate; not a separately added trust assumption. Deployment law/complete prior context association still required.'
change('V400','OPEN','Option B adopted by D248; failure signal is public to both experiments, bound/simE/complete observer unchanged. privacy_headline_deployed_B is a fixed-signal statement derived using the original refinement, not a proof of endogenous reached-failure independence. Full reached getrandom/filesystem failure independence and joint signal transport remain P. First-draw independence and conditional retry synchronization are narrower. Malformed compilation/programmed-oracle/control examples are not a checked admitted deployed-witness counterexample; option A not selected.',bucket='a',cls='P',ev=['optb:evidence/pv-optb-20261027/STATEMENT-DIFF.md','optb:evidence/pv-optb-20261027/INDEPENDENCE.md','optb:evidence/pv-optb-20261027/REPORT.md'],fields=['witness-independent reached failure event / source-to-endogenous-signal transport; no new OsAvailable T'])
change('V371','OPEN','D248 adopts DOITM-mode acceptance only. Secure Boot lockdown refuses raw MSR writes; support bit exists but IA32_UARCH_MISC_CTL=0 on all CPUs. Firmware/kernel configuration change is still needed. Explicit substantive L3 hardware T item retained; not an added field of the capped RunJoin record.',bucket='c',cls='T',ev=['research:design/PRIVACY-LEDGER-20261026.md#Owner decisions 2026-10-27 (B)'])
change('V370','OPEN','Compiler preservation is P under capped T: actual pinned compiler/flags and native witness-bearing kernels/calls must preserve the proved behavior. No extra compiler TrustItems field is adopted. No pending owner choice substitutes for that proof.',bucket='b',cls='P',ev=['LOG D248','research:design/RELEASE-LEDGER-20261025.md'])
change('V373','OPEN','Actual compiled-kernel and caller disassembly audit still required. D248 inversion handling is proof work, so this is independent evidence work rather than an owner-first boundary decision.',bucket='a',ev=['LOG D248','research:evidence/pv-inv3-20261027/OBSERVATION.md'])
change('V374','OPEN','D248 Docker-cap changes completed; quiet-window dudect/distribution evidence at the final pinned source remains to be supplied. Earlier D216 fixture medians do not supply this audit. Independent measurement/scheduling work; no unresolved owner policy decision.',bucket='a',ev=['LOG D248','research:design/RELEASE-LEDGER-20261025.md'])
change('V396','OPEN','Client bundle pin is now in research release ledger (1,295 tracked sources/12 roots, 16-step chain). Pinning closes that subtask only. Original row also requires exercising the actual caller/upload/key-retention failure/retry route and binding full client execution to FSExperiments.real/observe; those native/release integration facts remain P. No owner pin decision remains.',bucket='b',ev=['research:design/RELEASE-LEDGER-20261025.md'],fields=['actual caller/upload/failure/retry integration and headline source/observer association'])
change('V380-inversion','OPEN','D248 inversion is P. Rounds 1–3 prove conditional same-coin containment in existing poleBad at the same attempt, preserving P and the original coupling; charge remains 8*(4096/((2^31-1)^4-1)). Tail masks 48–63 and order/duplicate OR algebra now closed. Installed dynamic registry/banks/caller/Records, P-false guard outcomes, and complete limb/index/address/latency observation law remain OPEN. No checked admitted witness-dependent uncharged zero found; no change to bound, observer or simE.',bucket='b',ev=['research:evidence/pv-inv3-20261027/REPORT.md','research:evidence/pv-inv3-20261027/OBLIGATIONS.md','research:evidence/pv-inv3-20261027/OBSERVATION.md'])
change('V183','OPEN','try_reserve_exact is not a pure value-only library row: recoverable native allocation failure/effects require RunJoin world/error interpretation. CBL explicitly defers it; no allocator behavior is erased or accepted as a fourth T field.',bucket='b',ev=['cblib:evidence/pv-cblib-20261027/NATIVE-EFFECTS.md'])
# Exact shared guard inventory: 15 operation rows, one (op223) now closed by applied route (ii).
inv=read('extract','evidence/pv-extract-20261027/INVENTORY.md')
for line in inv.splitlines():
 match=re.match(r'\| (\d+) / (V\d+) \|',line)
 if not match:continue
 op,id=match.groups();r=by[id];r['shared_obstruction']=line.strip('| ').replace(' | ','; ')
 if r['recount4_status']=='OPEN':
  r['dependency_bucket']='d';r['recount4_basis']='Shared extraction obstruction: '+r['shared_obstruction']+'. Guard is whole-crate/helper output scanning. Removing it privately still yields Aeneas loop-context abstraction remapping failure/no emission; no bypass is accepted. Route (ii) design candidate only for this row; only op223 is approved/applied. '+('The op36 logs concern candidate-owned adapters, not a rejection theorem for the shipped generic conversion. ' if op=='36' else '')+r['recount4_basis']
  r['recount4_evidence']+=['extract:evidence/pv-extract-20261027/INVENTORY.md','extract:evidence/pv-extract-20261027/ROOT-CAUSE.md']
# The ongoing CBL continuation adds two exact escaping-reference failures after the extraction inventory snapshot.
for id,pattern in [('V178','op26 mutable-reference join adapter: escaping-reference-output guard; owned adapter also retains structured Drop'),('V182','op31 exact push_str: escaping-reference-output guard')]:
 by[id]['dependency_bucket']='d';by[id]['shared_obstruction']=pattern
 by[id]['recount4_basis']='Later CBL continuation: '+pattern+'. Bounded native view/append checks do not supply a source law. Same shared extraction bucket as D257; route(ii) remains design-only for this row, not approved implementation work.'
 by[id]['recount4_evidence']+=['cblib:evidence/pv-cblib-20261027/RESUME.md']
by['V260']['recount4_basis']='op253 has an internal shared-loan cleanup failure after passing the preflight, distinct from the 15-row escaping-reference obstruction. Remains independent extraction/proof work (a), not bucket d. '+by['V260']['recount4_basis']
# Source snapshots support closure assertions; keep unpublished or reference-only rows unresolved.
for id in ['V228','V229','V230','V201']:
 by[id]['recount4_basis']+=' CBmid supplies reference equations/support only: zero row closures. No shipped/reference association inferred.'
 by[id]['recount4_evidence']+=['cbmid:docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CBM_CallbackBundle.lean','LOG D253']
# OPEN reachability remains a source/control proof slice, distinct from selected-record native binding.
for id in ['V404','V405']:
 by[id]['recount4_basis']='Complete admitted-input reached sets/exclusions still unproved. Static import chains are not execution witnesses; universally excluded callback entries remain none proved. This fixture source/control slice overlaps V163 native completion but is not a separate callback inventory decrement.'
# Explicit rows participating in overlapping obligations.
for id,target in [('V164','V240'),('V406','V329'),('V404','V163'),('V405','V163'),('V380-inversion','V373')]:by[id]['overlap_recount4']=target
# Import audit: actual roots only, exact source graph, never infer membership from row labels.
roots=[('research','R1Z.PrivacyR1HeadlineDeployedReal'),('join','R1Z.PV_Join_Wire_FinalAuditA'),('join','R1Z.PV_Join_PublicCaller'),('rw','R1Z.ProverRw19CanonicalAuditRefinement'),('rw','R1Z.ProverRw18ContextData'),('op223','R1Z.PV_Op223_V164')]
closures=[]
for k,root in roots:
 paths={root:[root]};queue=[root];unresolved=[]
 for m in queue:
  # Restrict recursive expansion to repository privacy namespaces; external boundaries explicit.
  if not m.startswith(('R1Z.','R0Z.')):continue
  s,path=module(k,m)
  if s is None:unresolved.append(m);continue
  for dep in re.findall(r'^import\s+(\S+)',s,re.M):
   if dep not in paths:paths[dep]=paths[m]+[dep];queue.append(dep)
 closures.append(dict(ref=k,root=root,paths=paths,unresolved_project_modules=unresolved))
wire=read('join','evidence/pv-join-20261026/wire/IMPORT-CHAIN.md');wireaudit=[]
for line in wire.splitlines():
 if not re.match(r'\| V\d+',line):continue
 c=line.split('|');id=c[1].strip();th=c[3].strip(' `');ms=re.findall(r'`([^`]+)`',c[4]);valid=True
 if id!='V270':
  for left,right in zip(ms,ms[1:]):
   s,_=module('join',left);valid=valid and s is not None and right in re.findall(r'^import\s+(\S+)',s,re.M)
  s,_=module('join',ms[-1]);valid=valid and s is not None and th.split('.')[-1] in s
 wireaudit.append(dict(id=id,theorem=th,modules=ms,edges_valid=valid,source='wire/IMPORT-CHAIN.md'))
 assert valid,id
assert len(wireaudit)==27
for r in rows:
 ws=[];th=r.get('closure_theorem') if r['recount4_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  m='.'.join(th.split('.')[:2]);own='op223' if r['id'] in ['V164','V240'] else 'cblib' if r['closure_route']=='P6 gate' and r['id']!='V195' else 'cb3' if r['id'] in ['V195','V219','V242','V254'] else 'cb'
  canonical,_=module(own,m);assert canonical and th.split('.')[-1] in canonical,(r['id'],th)
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
 r['in_headline_closure4']='research' if any(x['ref']=='research' for x in ws) else 'candidate' if ws else 'neither';r['import_witnesses4']=ws
 if r['recount4_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in ['a','b','c','d'],r['id']
# Same 27-row wire claim checked separately from newly scoped candidate closures.
assert sum(by[x['id']]['in_headline_closure4']=='candidate' for x in wireaudit)==26
counts=dict(rows=len(rows),classes=dict(collections.Counter(r['recount4_class'] for r in rows)),statuses=dict(collections.Counter(r['recount4_status'] for r in rows)),open_dependencies=dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount4_status']=='OPEN')),closure_routes=dict(collections.Counter(r['closure_route'] for r in rows if r['recount4_status']=='CLOSED-ON-CANDIDATE')),candidate_closure_imports=dict(collections.Counter(r['in_headline_closure4'] for r in rows if r['recount4_status']=='CLOSED-ON-CANDIDATE')),all_row_imports=dict(collections.Counter(r['in_headline_closure4'] for r in rows)))
counts['open_bucket_delta']={k:counts['open_dependencies'].get(k,0)-v for k,v in dict(a=44,b=51,c=8,d=0).items()};counts['premises_removed_added_weakened']=[0,0,0]
for name,obj in [('rows4.json',rows),('totals4.json',counts),('definition-audit4.json',audit),('manifest.json',manifest),('import-closures4.json',closures),('wire-audit4.json',wireaudit)]: (P/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
lines=['# Recount 4 2026-10-27 (B)','','All 407 original rows re-derived. Historical statements/classes remain intact; current classes apply D248. Candidate closure suffix is its route. Import membership is not deployed discharge. P6 gates retain their exact bounds/carriers. See recount4/METHOD4.md, pins.json, definition-audit4.json and rows4.json for source hashes and import witnesses. Target not yet established.','','| Row / class 3 → 4 / name | Status 3 → 4 | OPEN bucket | in headline closure? | Derivation, retained obligation and evidence |','|---|---|---|---|---|']
for r in rows:
 status=r['recount4_status']+(' ('+r['closure_route']+')' if r['recount4_status']=='CLOSED-ON-CANDIDATE' else '')
 detail=r['recount4_basis']+' Residual: '+'; '.join(r.get('residual_fields',[]))+'. Evidence: '+'; '.join(r['recount4_evidence'])+'. Full witnesses: recount4/rows4.json#'+r['id']
 lines.append('|'+r['id']+' / '+r['classification']+' → '+r['recount4_class']+' / '+r['name'].replace('|','\\|')+'|'+r['recount3_status']+' → '+status+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure4']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(P/'used-sources4.json').write_text(json.dumps(sorted(used),indent=2)+'\n')
(BASE/'ROWS4.md').write_text('\n'.join(lines)+'\n');print(json.dumps(counts,indent=2))
