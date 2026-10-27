"""Recount the fresh Rc8 kernel inventory, with preserved ledger row identities."""
from pathlib import Path
from collections import Counter
import copy,hashlib,json,re
E=Path(__file__).resolve().parent; R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
basefile=R/'evidence/recount7-20261026/Rc7_premises.json'
base=json.loads(basefile.read_text()); baseline={x['id']:x for x in base['rows']}
log=(E/'Rc8_007/stdout.log').read_text()
for name,label in [('Rc7_Top.deployed','BEFORE'),('FIo_Accepted.deployed','BEFORE_INSTALLED'),('FGm_Headline.deployed','GLOBAL_PREDECESSOR'),('Rc8_Top.deployed','AFTER'),('Rc8_Nonvacuity.composed','NONVACUITY')]:
 start=log.index('@AspisR1.'+name+' :');end=log.find('\n@AspisR1.',start+1)
 if end<0:end=log.index("\n'AspisR1.Rc8_Top.deployed' depends",start)
 (E/('Rc8_'+label+'.lean.txt')).write_text(log[start:end].rstrip()+'\n')
# The kernel statement must have precisely the FGm antecedent and old result,
# with only the derived S6 certificate conjoined. Whitespace is pp context.
normalize=lambda s:re.sub(r'\s+',' ',s).strip()
global_stmt=(E/'Rc8_GLOBAL_PREDECESSOR.lean.txt').read_text()
after=(E/'Rc8_AFTER.lean.txt').read_text()
global_n=normalize(global_stmt.replace('FGm_Headline.deployed','Rc8_Top.deployed'))
after_n=normalize(after)
installed=(E/'Rc8_BEFORE_INSTALLED.lean.txt').read_text()
assert normalize(installed.replace('FIo_Accepted.deployed','FGm_Headline.deployed').replace('FGl_PreparedAt.Owners','FGm_Owners.Owners'))==normalize(global_stmt), 'Unexpected installed before/after change'
assert 'AspisR1.FGm_Owners.Owners' in after_n
assert 'AspisR1.FGl_PreparedAt.Owners' not in after_n
assert after_n.startswith(global_n+' ∧ AspisR1.S6N_Installation.Facts'), 'Unexpected before/after statement change'
# Explicit fresh leaf inventory: T and G boundary leaves audited independently;
# only the local continuation and five global families feed the finish gate.
trust=[r['id'] for r in base['rows'] if r['classification']=='T']
game=[r['id'] for r in base['rows'] if r['classification']=='G']
native=['L'+str(n) for n in [133,134,135,136,137,138,142,143,144,145,146,147]]
global_ids=['F3Y_G_L'+str(n) for n in [142,143,144,145,146]]
conditions=['L154','L159']; deployment=['L166','L181','L187','L188']; aliases=['L185']
fresh_ids=set(trust+game+native+global_ids+conditions+deployment+aliases)
rows=[]
for r in base['rows']:
 if r['id'] not in fresh_ids: continue
 x=copy.deepcopy(r)
 x['evidence']='Rc8 fresh kernel statement007; law-family expansions008–051; installed/global audit053/054'
 if x['classification']=='P':
  rid=x['id']; leaf=rid.removeprefix('F3Y_G_')
  job='UNCOVERED'
  if leaf in ['L142','L143','L144','L145','L146']:job='FIp_'
  elif rid in ['L159','L185','L181']:job='SCH_'
  elif rid=='L166':job='BEf_'
  elif rid=='L187':job='RPz2_'
  x['running_job']=job
  if rid in ['L133','L135','L136','L138']:
   x['blocker']='FIn field/add/polynomial are installed. The returned native continuation still assumes this round law; the SAME native tx2.v2 byte-view/model polynomial join is not exported there. FIn_FromRead.rounds requires SAG_NativeFull.Shape; Cons_Native.Calls alone does not retain that provenance. Global FGm derivation is a separate quantified domain.'
  elif rid in ['L134','L137']:
   x['blocker']='Quarter/mulM are installed. Their identical quarter predicate is still explicitly assumed inside the native continuation; Rc8 does not strengthen that continuation to consume the installed quarter semantics. Count once by FIn_QuarterAlias, without claiming a missing abstract operational slot.'
  elif leaf=='L142':
   x['blocker']='Complete native constructor and Pair are installed, but SAME literal-input coefficient/challenge/FunctionalWeights/dual-fold model-value refinement is still assumed. Installation alone is not this law.'
  elif rid=='L147':
   x['blocker']='SAG_DotClosed.source is installed. Native continuation still assumes the final64 dot meaning; deriving it there requires SAME native View final_message byte provenance plus actual accumulator weights. FIo_Derived.derive requires shape/aux/read joins not retained by Calls alone.'
  elif rid=='L159':
   x['blocker']='Exact frozen3 StoredCarrierBinding at FIo_Install.configuration for this SAME source/prover/runtime remains a hypothesis. The fixture runtime is not arbitrary deployed-runtime association.'
  elif rid.startswith('F3Y_G_'):
   x['blocker']='FGm_Owners.Owners/Holds retains this global family on the SAME accepted Evidence, prepared input and native finish witness. Full Pair value, matching and semantic endpoint source/model bindings are still not supplied by installing finish arithmetic.'
  if rid in native:
   x['definition']='lean/SAF_C_SAF_FinishPrepared.lean#Outcome; lean/SAF_ReducedLaws.lean#Arithmetic'
  if rid.startswith('F3Y_G_'):x['definition']='lean/FGm_Owners.lean#Owners/Holds'
 rows.append(x)
assert {r['id'] for r in rows}==fresh_ids
removed=set(baseline)-fresh_ids
assert removed=={'F3Y_G_L'+str(n) for n in [133,134,135,136,137,138,147]}|{'L176'}
def tally(rs):
 return dict(rows=len(rs),classes={c:sum(r['classification']==c for r in rs) for c in ['T','P','G','C']},by_owner={o:{c:sum(r['classification']==c and r['owner']==o for r in rs) for c in ['T','P','G','C']} for o in ['lead','session A','external']})
def scopes(rs):
 return {s:tally([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}|{'deduplicated actual plus non-alias deployment':tally([r for r in rs if r['scope']!='deployment alias'])}
distinct=lambda rs:[r for r in rs if r['id'] not in ['L137','F3Y_G_L137']]
raw=scopes(rows); counts=scopes(distinct(rows)); old=scopes(distinct(base['rows']))
assert counts['actual antecedent']['classes']==dict(T=83,P=18,G=13,C=0)
assert counts['deduplicated actual plus non-alias deployment']['classes']==dict(T=89,P=22,G=13,C=0)
diff=[dict(id=rid,change='retained' if rid in fresh_ids else 'removed',classification=r['classification'],owner=r['owner'],scope=r['scope'],proof=('S6N_Installation.facts; Rc8_Top.deployed last conjunct' if rid=='L176' else 'FGm_Aligned/Canonical/Join/Bound; Rc8_Top.deployed same installed finish') if rid in removed else None) for rid,r in baseline.items()]
result=dict(actual_theorem='AspisR1.Rc8_Top.deployed',baseline='AspisR1.Rc7_Top.deployed',method=base['method'],baseline_sha256=sha(basefile),counts=counts,raw_counts=raw,before_distinct=old,distinct_delta=dict(T=0,P=-7,G=0,C=0),raw_nonalias_delta=dict(T=0,P=-8,G=0,C=0),removed=sorted(removed),added=[],rows=rows,diff=diff,aliases={'L137':'L134','L185':'L159'},fixture_gate={'job':'JFt_','status':'OPEN; not a further independent ledger P row'},native_removals=[],nonvacuity='Rc8_Nonvacuity.composed, Rc8_Clean.exists_world: conditional accepted executions/positive margin and non-universal collision branch; joint release fixture remains OPEN')
(E/'Rc8_premises.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# Rc8 fresh mechanical recount','','Ledger identities are retained; fresh kernel statements and expanded boundary definitions determine inclusion. Native and source-global witness domains remain separate. L137 is the same quarter predicate as L134; L185 aliases L159.','', '|Scope|Rc7 distinct T/P/G|Rc8 distinct T/P/G|','|---|---:|---:|']
for s in counts:
 lines.append('|'+s+'|'+'/'.join(str(old[s]['classes'][k]) for k in ['T','P','G'])+'|'+'/'.join(str(counts[s]['classes'][k]) for k in ['T','P','G'])+'|')
lines+=['','Distinct delta **−7 P**: six global finish families plus deployment L176. Raw nonalias delta −8 rows because two global quarter fields represented one predicate. No native-local finish premise has been removed. No new T/P/G/C.','', '|Remaining P row|Owner|Scope|Covering job|','|---|---|---|---|']
for r in rows:
 if r['classification']=='P': lines.append('|'+r['id']+'|'+r['owner']+'|'+r['scope']+'|'+r['running_job']+'|')
lines+=['','JFt_ covers the separate joint fixture/non-vacuity gate. It is OPEN and is not invented as a further P row. SCH_/FIp_/BEf_/RPz2_ are assignments only; no concurrent result is credited. L188 and the native-local rounds/dot plus query-budget deployment association remain UNCOVERED.','', '|Removed row|Proof path|','|---|---|']
for r in diff:
 if r['change']=='removed':lines.append('|'+r['id']+'|'+r['proof']+'|')
lines+=['','Before/after: Rc8_BEFORE.lean.txt and Rc8_AFTER.lean.txt; Rc8_BEFORE_INSTALLED.lean.txt displays the already FIo-specialised predecessor. The carrier F is specialised to FIo_Install.W and the complete Pair dictionary; no all-seed claim is made. Game, failure event, source selector and numerical constants are unchanged.','', 'Conditional non-vacuity is checked by Rc8_Nonvacuity.composed using the actual new top and the SAME accepted native cuts/snapshots, yielding actual source/runtime acceptance and a positive zero-query margin. It retains the five global laws; full joint release inhabitation is not established. Rc8_Clean.exists_world proves the charged event is not universal.']
(E/'Rc8_LEDGER.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'counts':counts,'removed':sorted(removed)},indent=2))
