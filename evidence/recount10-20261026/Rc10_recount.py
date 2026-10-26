"""Recount current kernel root and expanded quantified families against Rc9 identities."""
from pathlib import Path
from collections import Counter
import copy,hashlib,json,re
E=Path(__file__).resolve().parent; R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
norm=lambda s:re.sub(r'\s+',' ',s).strip()
basefile=R/'evidence/recount9-20261026/Rc9_premises.json'
b=json.loads(basefile.read_text())
def output(module):
 matches=[]
 for p in sorted(E.glob('Rc10_*/receipt.json')):
  d=json.loads(p.read_text())
  if d['exit_status']==0 and module+'.lean' in d['sources']:matches.append(p.parent/'stdout.log')
 assert matches,module
 return matches[-1].read_text()
log=output('Rc10_Statements')
parts={}
for name,label in [('Rc9_Top.deployed','BEFORE'),('FIs_Top.deployed','FIS'),('Rc10_Top.deployed','AFTER'),('Rc10_Nonvacuity.composed','NONVACUITY')]:
 start=log.index('@AspisR1.'+name+' :')
 end=re.search(r"\n(?:@AspisR1\.|'AspisR1\.)",log[start+1:])
 finish=start+1+end.start() if end else len(log)
 parts[label]=log[start:finish].rstrip()+'\n'
 (E/f'Rc10_{label}.lean.txt').write_text(parts[label])
assert norm(parts['FIS'].replace('FIs_Top','Rc10_Top'))==norm(parts['AFTER'])
assert norm(parts['BEFORE'].replace('Rc9_Top','Rc10_Top').replace('P2P_Result.Outcome','FIs_Result.Outcome'))==norm(parts['AFTER']), 'Unaccounted quantifier/event/carrier/installation or conclusion change'
# Re-open every atomic-family inventory on this root; never count visible binders only.
plan=json.loads((E/'Rc10_audit-plan.json').read_text())
audit={m:output(m) for m in plan}
for m in plan:assert 'error:' not in audit[m]
finish=audit['Rc10_AuditFinish']; global_=audit['Rc10_AuditGlobalOwners']; laws=audit['Rc10_AuditFinishLaws']
for t in ['FIs_Finish.Outcome','FIs_Pair.Law','MatchingSupport.match0','EquationEndpoint']:
 assert t in finish,t
# The old guarded native Arithmetic and dot inputs are absent from the actual finish continuation.
start=finish.index('def AspisR1.FIs_Finish.Outcome')
finishdef=finish[start:finish.index('structure AspisR1.RowFinish_Control.RoundValues',start)]
assert 'SAF_ReducedLaws.Arithmetic' not in finishdef
assert 'dot_S5' not in finishdef and 'RoundLaws' not in finishdef
for t in ['FIp_GlobalOwners.Owners','FIp_Remaining.Holds','SAG_NativeFull.Shape','PairMeaning','EquationEndpoint']:
 assert t in global_,t
for t in ['RoundLaws','quarter','boundary','eval','MatchingSupport.match0','EquationEndpoint']:
 assert t in laws,t
for m,t in [('ResultBinding','FIs_Caller.Outcome'),('Literal','FIs_Literal.Outcome'),('Continuation','FIs_Cont.Outcome'),('Sdk','S2TrustedSdkBorrow'),('Extraction','AeneasExtraction'),('Game','DeployedPairExecution'),('Persistence','TwoTransactionLaw')]:
 assert t in audit['Rc10_Audit'+m],(m,t)
removed={f'L{n}' for n in [133,134,135,136,137,138,147]}
assert {r['id'] for r in b['rows'] if r['id'] in removed}==removed
assert all(r['classification']=='P' and r['scope']=='actual antecedent' for r in b['rows'] if r['id'] in removed)
rows=[]
for old in b['rows']:
 if old['id'] in removed:continue
 r=copy.deepcopy(old);rid=r['id'];leaf=rid.removeprefix('F3Y_G_')
 r['evidence']='Rc10_Statements full kernel root; Rc10_Audit* fresh expanded atomic families; Rc10_NativeRetention'
 if r['classification']=='P':
  job='UNCOVERED'
  if leaf in ['L142','L143','L144','L145','L146']:job='FIr_'
  elif rid in ['L159','L185','L181']:job='ARQ_'
  elif rid=='L166':job='BEh_'
  elif rid=='L187':job='RPz3_'
  r['running_job']=job
  if leaf in ['L142','L143','L144','L145','L146']:
   r['blocker']='SAME native-local or source-global Pair/matching/semantic family remains; full operands, canonicality and exact masked terminal association are not supplied by concrete primitive installation.'
   if not rid.startswith('F3Y_G_'):r['definition']='lean/FIs_Finish.lean#Outcome; lean/FIs_Pair.lean#Law'
  if rid=='L181':
   r['meaning']='Residual full deployed native/source rejected-prefix and ordered-query association. Accepted source ordered-log/result join OR the charged collision is already composed under frozen3; no exact frozen2 log premise is required.'
  if rid=='L142':
   r['meaning']='For the SAME native view/prepared/data, every successful newWeights, alpha-slice and pair return decodes to the model dot of final values with both dual folds of FunctionalWeights.'
  if rid=='L159':
   r['definition']='lean/F3T_Runtime.lean#StoredCarrierBinding'
   r['meaning']='∀ H run, (eval H runtime).2 = some run → run.2.2 = true → run = eval H (annotatedWith D rust (F3T_Canon.canon (lift c P))). Entire accepted runtime run equals the canonical installed-source experiment on the SAME P.'
  if rid=='L154':
   r['definition']='lean/Rc10_Top.lean#deployed.queries'
   r['meaning']='∀ H : Bytes → State, (eval H P).1.length ≤ Q0 + Q1. Bound on all issued ByteProver oracle queries including repeats, uniformly over ideal worlds; external adversary budget condition, not a cryptographic axiom or proved concrete deployment budget.'
   r['blocker']='Retained external query-budget condition. Any concrete workload claim must justify this total issued-query bound in the adopted work model. No current covering worker.'
  if rid=='L188':r['blocker']='Final source/object/tool/runtime/adoption/trust and dependency axioms audit after coherent RPz3_ release replay; focused checks here do not close it.'
 rows.append(r)
def tally(rs):
 return dict(rows=len(rs),classes={c:sum(r['classification']==c for r in rs) for c in ['T','P','G','C']},by_owner={o:{c:sum(r['classification']==c and r['owner']==o for r in rs) for c in ['T','P','G','C']} for o in ['lead','session A','external']})
def scopes(rs):
 return {s:tally([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}|{'deduplicated actual plus non-alias deployment':tally([r for r in rs if r['scope']!='deployment alias'])}
raw=scopes(rows);counts=scopes([r for r in rows if r['id']!='L137'])
assert counts['actual antecedent']['classes']==dict(T=83,P=12,G=13,C=0)
assert counts['deduplicated actual plus non-alias deployment']['classes']==dict(T=89,P=16,G=13,C=0)
assert [r['id'] for r in rows if r['classification']=='P' and r['owner']=='external']==['L154']
diff=[dict(id=r['id'],change='removed' if r['id'] in removed else 'retained',classification=r['classification'],owner=r['owner'],scope=r['scope'],meaning=r.get('meaning'),definition=r.get('definition')) for r in b['rows']]
for d in diff:
 if d['change']=='retained':
  new=next(r for r in rows if r['id']==d['id'])
  d['after_meaning']=new.get('meaning');d['after_definition']=new.get('definition')
result=dict(actual_theorem='AspisR1.Rc10_Top.deployed',baseline='AspisR1.Rc9_Top.deployed',method=b['method'],baseline_sha256=sha(basefile),counts=counts,raw_counts=raw,distinct_delta=dict(T=0,P=-6,G=0,C=0),raw_nonalias_delta=dict(T=0,P=-7,G=0,C=0),removed=sorted(removed),added=[],rows=rows,diff=diff,aliases={'L185':'L159'},removed_alias={'L137':'L134'},fixture_gate={'job':'JFr_','status':'OPEN; separate joint inhabitation gate, no fictional extra premise'},native_removals=sorted(removed),global_removals=[],dictionary_change='None from Rc9: SAME FIp_Install.configuration. Rc10_Install.compatible and finish_preserved.',reverse='Rc10_Reverse.transport maps the supplied complete Rc10 result to Rc9 conclusion through Rc10_Result/Caller/Cont/Literal.forget and FIs_Finish.forget; all existential tuples, guards and collision branches preserved.',nonvacuity='Rc10_Nonvacuity.composed invokes this root conditionally on SAME accepted native cuts/snapshots; Rc10_Clean.exists_world excludes universal charged event; full JFr fixture remains OPEN.')
(E/'Rc10_premises.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'Rc10_row-diff.json').write_text(json.dumps(diff,indent=2)+'\n')
(E/'Rc10_statement-check.json').write_text(json.dumps({'Rc9_to_Rc10':'identical full kernel statements after root renaming and P2P_Result.Outcome -> FIs_Result.Outcome only','FIs_to_Rc10':'identical modulo root name','before_sha256':sha(E/'Rc10_BEFORE.lean.txt'),'after_sha256':sha(E/'Rc10_AFTER.lean.txt'),'new_assumptions':[],'changed_quantifiers_events_carriers_constants':[]},indent=2)+'\n')
lines=['# Rc10 mechanical recount','','Actual root: `AspisR1.Rc10_Top.deployed`. Full before/after statements are Rc10_BEFORE/AFTER.lean.txt. The full kernel signatures differ only by the strengthened returned Outcome. All source-global/native-local guards and shared existential witnesses remain.','','| Basis | T | P | G | C |','|---|---:|---:|---:|---:|']
for label,d in [('Raw actual',raw['actual antecedent']),('Raw deployment',raw['deployment only']),('Raw deployment alias L185',raw['deployment alias']),('Raw non-alias combined',raw['deduplicated actual plus non-alias deployment']),('Distinct actual',counts['actual antecedent']),('Distinct non-alias combined',counts['deduplicated actual plus non-alias deployment'])]:
 c=d['classes'];lines.append(f"| {label} | {c['T']} | {c['P']} | {c['G']} | {c['C']} |")
lines+=['','Rc9 → Rc10: seven raw native rows removed (L133–L138/L147); six independent families because L137 aliased L134. Delta **0T/−6P/0G/0C**, no additions, global removal zero. No T/G reclassification.','','| Owner, distinct combined | T | P | G |','|---|---:|---:|---:|']
for owner,c in counts['deduplicated actual plus non-alias deployment']['by_owner'].items():lines.append(f"| {owner} | {c['T']} | {c['P']} | {c['G']} |")
lines+=['','Every remaining P row, including deployment aliases and external conditions:','','| Row | Scope | Owner | Exact statement summary | Covering job |','|---|---|---|---|---|']
for r in rows:
 if r['classification']=='P':lines.append(f"| {r['id']} | {r['scope']} | {r['owner']} | {r['meaning']} | {r['running_job']} |")
lines+=['','Source-global F3Y_G_L142–L146 quantify over every source Evidence/world/installed accepted witness, guarded by the derived SAME-witness Shape. Native L142–L146 occur on the one returned native continuation. They are ten independent families, not five aliases. L144–L146 retain SAME EquationEndpoint parsing/view/claim guards. Native L142 retains actual newWeights/alpha-slice/pair success guards in FIs_Pair.Law.','','The ONLY external P is L154: the uniform total issued-query budget on ByteProver, including repeats. It is a condition on the adversary/query metric and remains P; it is not part of the 89 adopted external T rows. No covering worker is assigned. L185 aliases L159 and contributes no independent count. L188 is UNCOVERED pending RPz3_ replay and final audit. JFr_ covers the separate OPEN joint-fixture gate, not an invented ledger row.','','Non-vacuity: Rc10_Nonvacuity.composed invokes this actual root at zero ByteProver queries with SAME accepted native cuts and snapshots, producing source/runtime acceptance and positive numeric margin. Retained extraction/game/owner assumptions remain conditional. Rc10_Clean.exists_world excludes a universal charged event. These do not prove simultaneous inhabitation of all release premises; the SCE extraction obstruction in ARP remains relevant.','','No merged FIr_/ARQ_/BEh_ deployed top was available at the pinned start. Merged ARP and BEg explicitly retain their deployment rows; none is removed by a local observer theorem or a fixed-input diagnostic. Target not yet established.']
(E/'Rc10_LEDGER.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'counts':counts,'removed':sorted(removed),'delta':result['distinct_delta']},indent=2))
