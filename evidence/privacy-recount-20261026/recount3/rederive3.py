from pathlib import Path
import json,re,copy,collections,subprocess
P=Path(__file__).resolve().parent;OUT=P.parent
rows=copy.deepcopy(json.loads((OUT/'recount2/rows2.json').read_text()));by={r['id']:r for r in rows};pins=json.loads((P/'pins.json').read_text())
R='docs/research/v8-r0-zk-20261009/lean/R1Z/'
def snap(k,path):
 p=P/'snapshots'/k/path
 if p.exists():return p.read_text()
 return subprocess.check_output(['git','show',pins[k]+':'+path.removesuffix('.txt')]).decode()
def mod(k,m):return snap(k,R+m+'.lean.txt')
for r in rows:
 r['recount3_status']=r['recount2_status'];r['recount2_bucket']=r.get('dependency_bucket');r['recount3_basis']=r['recount2_basis'];r['recount3_evidence']=['definition-audit3.json',*r['recount2_evidence']];r['closure_theorem']=None
 # The row's historical definition and model/guard/data scope remain unchanged.
 if r['recount3_status']=='OPEN':r['recount3_basis']+=' No complete source/native/owner instance is supplied by the pinned branch evidence at this row scope.'
def change(id,status,why,bucket=None,theorem=None,ev=None,fields=None):
 r=by[id];r['recount3_status']=status;r['recount3_basis']=why;r['dependency_bucket']=bucket if status=='OPEN' else None
 if theorem:r['theorem']=theorem;r['closure_theorem']=theorem
 if ev:r['recount3_evidence']=['definition-audit3.json',*ev]
 if fields is not None:r['residual_fields']=fields
# Strict new source criterion: do not call selector installation a source closure.
for r in rows:
 if r.get('group')=='O' and r['recount2_status']=='CLOSED-ON-CANDIDATE':
  change(r['id'],'REDUCED','Recount 3 strict source criterion: historical selected/installed equation or selected reference interpretation is available, but not an accepted complete extracted-source theorem at this operation. Preserve the useful value installation; withdraw source-closure credit. This is a reporting correction, not a disproved equation.',ev=['checks.json','out-38607.log','out-38611.log'])
# Latest table is mapped by operation number to original row name, never by a LOG row label.
report=snap('cb','evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md');cbrows=[]
for line in report.splitlines():
 if 'ROW-DISCHARGED(candidate)' not in line:continue
 cells=line.split('|');op=int(cells[1]);theorem=cells[4];r=next(r for r in rows if r.get('group')=='O' and re.match(r'op'+str(op)+r'\b',r['name']))
 assert r['id']==cells[2],(op,r['id'],cells[2])
 m=theorem.split('.')[1];s=mod('cb',m);assert re.search(r'(?:theorem|abbrev)\s+op'+str(op)+r'_source\b',s),(op,m)
 why='Complete extracted source Result equation for arbitrary declared inputs; nominal carrier conversions are explicit and all failure/divergence outcomes remain. D188 extraction boundary retained. Native effects, carrier/world and release association remain V165–V167. '+cells[5].replace('restored replay','prior restored replay')
 change(r['id'],'CLOSED-ON-CANDIDATE',why,theorem=theorem,ev=['snapshots/cb/evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md','checks.json',f'snapshots/cb/{R}{m}.lean.txt'],fields=[]);cbrows.append(r['id'])
assert len(cbrows)==23
for op in [120,225,246]:
 r=next(r for r in rows if r.get('group')=='O' and re.match(r'op'+str(op)+r'\b',r['name']));m='PV_CB3_Op'+str(op)+'Source';assert 'theorem op'+str(op)+'_source' in mod('cb3',m)
 change(r['id'],'CLOSED-ON-CANDIDATE','Complete extracted source Result equation in CB3, composed in CallbackBundle. All unrelated callbacks remain arbitrary; source/native/release joins are retained. This row is distinct from V246/op229.',theorem='R1Z.'+m+'.op'+str(op)+'_source',ev=['out-38606.log','snapshots/cb3/evidence/pv-cb3-20261026/HANDOFF.md',f'snapshots/cb3/{R}{m}.lean.txt'],fields=[])
change('V203','REDUCED','op81 selected heap interpretation and caller specialization exist, but the current 23/73 extracted-source inventory does not credit op81. PV_CB_Op81Source is an older selected-reference equation, not fresh extracted shipped Vec allocation source. Keep the useful caller/dictionary bridge; stricter source-closure credit withdrawn.',ev=['snapshots/cb/evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md','snapshots/join/evidence/pv-join-20261026/resume/FINAL-REPORT.md'])
change('V195','OPEN','op51 withdrawal required by this recount remains in force. Historical PV_CB3_Op51Source selects extracted owned wide_bytes_flat, not the shipped whole body. The later cb5 report claims arbitrary-eight-u32 native P6 coverage and PV_CB3_Op51Arbitrary.op51_source (checked at 38606), but that theorem wraps the same reference selection. We record this newer claim without overriding the explicit withdrawal or counting a bounded native gate as a new shipped-source theorem.',bucket='a',ev=['out-38606.log','snapshots/cb3/evidence/pv-cb3-20261026/HANDOFF.md','snapshots/cb3/evidence/pv-cb3-20261026/RESUME_FINAL.json'],fields=['arbitrary-carrier shipped/extracted-source correspondence; owner recount withdrawal'])
change('V164','REDUCED','rw18/rw20 source decomposition and concrete context identity are checked. Remaining single hypothesis P_source_p6 identifies ops.op223 with ProverRwP6CompressSource.compress under PV_CurrentScaleInstall.selected. This is V240/op223, not an extra independent row. Context identity is discharged; original shipped-helper correspondence is not.',ev=['out-38609.log','snapshots/rw/evidence/pv-rw19-resume-20261026/FINAL-REPORT.md'],fields=['P_source_p6 / V240 op223'])
change('V163','OPEN','Concrete deployed-input-to-mathematical-model construction and complete proof-byte/data equations remain missing. Canonical audit and independent serializer exist (later ProverRw21ModelInstance is published), but do not instantiate the deployed caller. Original refinement_of_data has an ExternalFuns parameter, reservation and whole-data equation; no callback-hypothesis list. Both fixtures and general equation OPEN.',bucket='b',ev=['out-38610.log','out-38617.log','snapshots/rw/evidence/pv-rw19-resume-20261026/FINAL-REPORT.md','snapshots/join/evidence/pv-join-20261026/resume5/FINAL-REPORT.md'],fields=['concrete deployed model construction; transfer/withdrawal/general proof bytes; V240 source law'])
by['V240']['recount3_basis']='Exact op223 source correspondence remains OPEN. This is the remaining P_source_p6 of V164, same obligation counted once. New owned-reference extraction does not prove shipped=reference or supply PV_CB_Op223Source.op223_source; generic slice lengths/full Result remain required.'
by['V240']['recount3_evidence']+=['snapshots/rw/evidence/pv-rw19-resume-20261026/FINAL-REPORT.md','snapshots/join/evidence/pv-join-20261026/resume5/FINAL-REPORT.md']
for id in ['V152','V153','V154']:
 change(id,'REDUCED','Source-identification interfaces and canonical source-stage laws reduce the row to five named families. words/publicCorr/admission/row_call REDUCED; compile_call OPEN. Deployed premises 5→5; reference 3. Concrete native returned compiler/carrier association is not provided. D231 merge gate blocked by stale cached object; newer resume6 additionally records a protected source replay failure, not a row counterexample. No whole deployment closure.',ev=['out-38612.log','out-38613.log','snapshots/srcid/evidence/pv-srcid3-20261026/RESUME5.md','snapshots/srcid/evidence/pv-srcid3-20261026/RESUME6.md'],fields=['words REDUCED','publicCorr REDUCED','admission REDUCED','row_call REDUCED','compile_call OPEN','merge/replay gate blocked'])
for id in ['V344','V345']:
 change(id,'EVIDENCED','D216 qualified quiet-host timing PASSED: transfer research/candidate medians 38.909/13.742 s, withdrawal 38.560/13.499 s; n=5 each, twenty quiet pre/post checks; candidate <15 s and <=1.10x. Fixture medians only, not universal constant-time/native refinement. Earlier invalidated windows retained.',ev=['snapshots/rebase/design/PV-REBASE-20261026.md','LOG D216'],fields=['pinned measurement scope; V340/V399 release association'])
change('V270','CLOSED-ON-CANDIDATE','D219 Formatter forbidden-axiom release-blocker audit: 12,920 declarations in 321 candidate family modules and endpoint roots have only propext/Classical.choice/Quot.sound. This closes the scoped inadmissible axiom-route diagnostic, not native Formatter adequacy V269 or a coherent release replay. Original 26201/26203 audit receipts reused; 38608 could not check a separate owned-coefficient helper because its object is missing.',ev=['LOG D219','formatter-HANDOFF.md','formatter-FORMATTER-CLOSURE.md','out-38608.log'],fields=['native Formatter type/value/sink/failure/world remains V269'])
by['V269']['recount3_basis']='OPEN for the original complete native Formatter type/value/effect row. D219 closes only the Formatter-axiom release-blocker slice shared with V270; no native type-27 adequacy (types remain 26/28). Calling the whole V269 CLOSED-ON-CANDIDATE would silently change its statement.'
by['V269']['recount3_evidence']+=['formatter-HANDOFF.md','LOG D219']
# Proposed T and constructed candidate P do not rewrite deployed obligations.
for id in ['V038','V045','V336','V337','V338','V339']:
 by[id]['recount3_basis']+=' Runjoin8 constructs initial and causal for its candidate; deployed P unchanged, runtime/boundary 2→2, eight fields 8→8, six residuals 6→6. Proposed T has three unchanged fields; adoption is V406.'
 by[id]['recount3_evidence']+=['snapshots/runjoin/evidence/pv-runjoin8-20261026/P-before-after.json','snapshots/runjoin/evidence/pv-runjoin6-20261026/trust-items.md']
def add(id,name,why,bucket,ev,fields):
 r=dict(id=id,name=name,meaning=name,classification='P',group='NEW3',recount1_status='NOT-PREVIOUSLY-SEPARATE',recount2_status='NOT-PREVIOUSLY-SEPARATE',recount3_status='OPEN',dependency_bucket=bucket,recount2_bucket=None,recount3_basis=why,recount3_evidence=ev,residual_fields=fields,theorem=None,closure_theorem=None);rows.append(r);by[id]=r
add('V403','M31 canonical domain at op121 callers (D234)','Prove every M31 reaching op121 from actual caller producers is in [0,P). Retained challenge 2^31 is noncanonical: it refutes only the unrestricted Horner replacement, not selected entry=self extraction. Producer polynomial/interpolation canonicality has later partial source lemmas; challenge semantic/update/read composition and full reached-domain invariant remain OPEN. This is a proof obligation, never new accepted trust.', 'a',['LOG D234','snapshots/join/evidence/pv-join-20261026/resume4/FINAL-REPORT.md','snapshots/join/evidence/pv-join-20261026/resume5/FINAL-REPORT.md'],['producer constructors/reducers/parsers and challenge-side invariant; overlap V220'])
for id,fixture in [('V404','transfer'),('V405','withdrawal')]:
 add(id,fixture+' per-fixture execution reachability','Determine the actual execution-reached entries and prove any exclusion for all admitted '+fixture+' inputs. Static import/dependency paths are not execution witnesses. Universally excluded set remains empty; conditional serialization-panic prefix and op226-first-after-entry do not establish reach/admission. Distinct fixture slice of V163; no new callback inventory decrement.','a',['snapshots/join/evidence/pv-join-20261026/resume4/FINAL-REPORT.md','snapshots/join/evidence/pv-join-20261026/resume5/FINAL-REPORT.md'],['complete reached set; all-admitted-input exclusion proofs; native fixture association remains V163/V167'])
add('V406','Owner adoption of proposed three-field trust list T','Owner decision pending for entropy_law (E1), entropy_kernel (joint 128-draw density), observation (native outcomes/filesystem/complete observer equal extracted execution). None is equality to the security experiment. Do not silently inflate accepted T or treat conditional candidate headline as deployed closure. A/B OS-failure repair remains separate V400.','c',['LOG D222','snapshots/runjoin/evidence/pv-runjoin6-20261026/trust-items.md','snapshots/runjoin/evidence/pv-runjoin8-20261026/P-before-after.json'],['accept/reject exact three-field T; actual deployed P and OS-failure A/B remain open'])
closures=json.loads((P/'import-closures.json').read_text());manifest=json.loads((P/'manifest.json').read_text()); mods={}
for x in manifest:
 if x['path'].startswith(R) and x['path'].endswith('.lean'):
  module='R1Z.'+Path(x['path']).stem;mods[x['ref'],module]=x
# Exact source hash must match consumer branch module, not merely the module name.
source_witnesses=[]
for r in rows:
 witnesses=[]
 th=r.get('closure_theorem')
 if th:
  module='.'.join(th.split('.')[:2]);own='cb3' if 'PV_CB3_' in module else 'cb';canonical=mods.get((own,module))
  for c in closures:
   target=mods.get((c['ref'],module))
   same_body=False
   if target and canonical:
    normalize=lambda x: re.sub(r'^import[^\n]*\n','',snap(x['ref'],x['path']),flags=re.M)
    same_body=normalize(target)==normalize(canonical)
   if module in c['paths'] and target and canonical and same_body:
    witnesses.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][module],source_sha256=canonical['sha256'],consumer_source_sha256=target['sha256'],binding='identical theorem/module body; import-only changes allowed'))
 elif r['id']=='V270':
  # A root axiom audit is not an imported closure theorem.
  witnesses=[]
 else:
  d=r.get('definition','').split('#')[0]
  if '/lean/' in d and d.endswith('.lean'):
   module=('R1Z.'+Path(d).stem) if '/lean/prover-rw-' in d else d.split('/lean/')[-1][:-5].replace('/','.')
   for c in closures:
    if module in c['paths']:witnesses.append(dict(ref=c['ref'],root=c['root'],path=c['paths'][module],scope='row definition/import presence only; not discharge'))
 # Three-way label: research has precedence if both, full witnesses retain overlaps.
 label='research' if any(w['ref']=='research' for w in witnesses) else 'candidate' if witnesses else 'neither'
 r['in_headline_closure']=label;r['import_witnesses']=witnesses
 if r['recount3_status']=='CLOSED-ON-CANDIDATE':source_witnesses.append(dict(id=r['id'],theorem=th,label=label,witnesses=witnesses))
for r in rows:
 if r['recount3_status']!='OPEN':r['dependency_bucket']=None
 if r['recount3_status']=='OPEN':assert r['dependency_bucket'] in ['a','b','c'],r['id']
def count(rs):return dict(rows=len(rs),classes=dict(collections.Counter(r['classification'] for r in rs)),statuses=dict(collections.Counter(r['recount3_status'] for r in rs)),open_dependencies=dict(collections.Counter(r['dependency_bucket'] for r in rs if r['recount3_status']=='OPEN')),candidate_closure_imports=dict(collections.Counter(r['in_headline_closure'] for r in rs if r['recount3_status']=='CLOSED-ON-CANDIDATE')),all_row_imports=dict(collections.Counter(r['in_headline_closure'] for r in rs)))
summary={'recount3_same403':count(rows[:403]),'recount3_all':count(rows),'source_equation_rows':len(cbrows)+3,'premises_removed':0,'premises_added':0,'premises_weakened':0}
(P/'rows3.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n');(P/'totals3.json').write_text(json.dumps(summary,indent=2)+'\n');(P/'closure-witnesses.json').write_text(json.dumps(source_witnesses,indent=2)+'\n')
lines=['# Recount 3 2026-10-27 (B)','','Every inherited row is re-derived against pinned git source and the evidence named below. Original rows, IDs, classes and scopes remain intact. OPEN buckets: a independent source work; b concrete native interpretation/model instance; c owner decision (owner-first). The import column records exact source/hash membership for candidate closures, and definition membership for other rows; it is not premise discharge. See recount3/METHOD3.md.','','| Row / class / original name | Recount 2 → recount 3 | OPEN dependency | in headline closure? (research / candidate / neither) | Statement basis, retained obligations and evidence |','|---|---|---|---|---|']
for r in rows:
 detail=r['recount3_basis']+' Residual: '+'; '.join(r.get('residual_fields',[]))+'. '
 if r.get('closure_theorem'):detail+='Source theorem: `'+r['closure_theorem']+'`. '
 detail+='Evidence: '+'; '.join(r['recount3_evidence'])+'. Import witness: `recount3/rows3.json#'+r['id']+'`.'
 lines.append('|'+r['id']+' / '+r['classification']+' / '+r['name'].replace('|','\\|')+'|'+r['recount2_status']+' → '+r['recount3_status']+'|'+(r['dependency_bucket'] or '—')+'|'+r['in_headline_closure']+'|'+detail.replace('|','\\|').replace('\n',' ')+'|')
(OUT/'ROWS3.md').write_text('\n'.join(lines)+'\n');print(json.dumps(summary,indent=2));print('closed neither',[(x['id'],x['theorem']) for x in source_witnesses if x['label']=='neither'])
