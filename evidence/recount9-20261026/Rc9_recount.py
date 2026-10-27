"""Fresh Rc9 kernel/family inventory with preserved accountable ledger identities."""
from pathlib import Path
from collections import Counter
import copy,hashlib,json,re
E=Path(__file__).resolve().parent; R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
norm=lambda s:re.sub(r"\s+"," ",s).strip()
basefile=R/'evidence/recount8-20261026/Rc8_premises.json'
base=json.loads(basefile.read_text())
log=(E/'Rc9_008/stdout.log').read_text()
parts={}
for name,label in [('Rc8_Top.deployed','BEFORE'),('FIp_Top.deployed','FIP'),('Rc9_Top.deployed','AFTER'),('Rc9_Nonvacuity.composed','NONVACUITY')]:
 start=log.index('@AspisR1.'+name+' :')
 end=re.search(r"\n(?:@AspisR1\.|'AspisR1\.)",log[start+1:])
 finish=start+1+end.start() if end else len(log)
 parts[label]=log[start:finish].rstrip()+'\n'
 (E/f'Rc9_{label}.lean.txt').write_text(parts[label])
after=norm(parts['AFTER']); fip=norm(parts['FIP'].replace('FIp_Top','Rc9_Top'))
assert after.startswith(fip+' ∧ AspisR1.S6N_Installation.Facts')
expected=norm(parts['BEFORE'].replace('Rc8_Top','Rc9_Top').replace('FIo_Install.configuration','FIp_Install.configuration').replace('FIo_Install.select','FIp_Install.select').replace('FGm_Owners','FIp_GlobalOwners'))
expected=expected.replace('.finish c.boundaries reservation','.finish (AspisR1.FIp_Install.boundaries c.boundaries) reservation')
assert expected==after,'Unaccounted before/after quantifier, event, trust or conclusion change'
# Read all distinct fresh expanded-family outputs, not a count of visible binders.
plan=json.loads((E/'Rc9_plan.json').read_text())
audit={mod:(E/f'Rc9_{n:03}'/'stdout.log').read_text() for n,mod in enumerate(plan,1) if (E/f'Rc9_{n:03}'/'stdout.log').exists()}
finish=audit['Rc9_AuditFinishLaws']; native=audit['Rc9_AuditFinish']; owners=audit['Rc9_AuditGlobalOwners']
for token in ['boundary','quarter','eval']:
 assert token in finish,token
for token in ['SAF_ReducedLaws.Arithmetic','MatchingSupport.match0','EquationEndpoint','CheckpointBytes5Output.ofE dot']:
 assert token in native,token
for token in ['FIp_GlobalOwners.Owners','FIp_Remaining.Holds','SAG_NativeFull.Shape','PairMeaning','EquationEndpoint']:
 assert token in owners,token
# PairMeaning + match0 + EquationEndpoint.initial/chain/terminal = five global families.
# Two guarded RoundLaws (3 each) + Pair + match + semantic (3) + dot = twelve native rows.
native_ids={f'L{n}' for n in [133,134,135,136,137,138,142,143,144,145,146,147]}
global_ids={f'F3Y_G_L{n}' for n in [142,143,144,145,146]}
assert not any(f'F3Y_G_L{n}' in {r['id'] for r in base['rows']} for n in [133,134,135,136,137,138,147])
rows=[]
for old in base['rows']:
 r=copy.deepcopy(old);rid=r['id'];leaf=rid.removeprefix('F3Y_G_')
 r['evidence']='Rc9_008 kernel statement; Rc9 fresh atomic family inventories009–052; native/global inventory055/056'
 if r['classification']=='P':
  job='UNCOVERED'
  if leaf in ['L142','L143','L144','L145','L146']:job='FIq_'
  elif rid in ['L159','L185','L181']:job='SCJ_'
  elif rid=='L166':job='BEg_'
  elif rid=='L187':job='RPz3_'
  elif rid=='L188':job='pending RPz3_ replay'
  r['running_job']=job
  if rid in native_ids:r['definition']='lean/SAF_C_SAF_FinishPrepared.lean#Outcome; lean/SAF_ReducedLaws.lean#Arithmetic'
  if rid in global_ids:
   r['definition']='lean/FIp_GlobalOwners.lean#Owners; lean/FIp_Remaining.lean#Holds'
   r['blocker']='Five global Pair/matching/semantic laws remain on SAME source Evidence/native witness, with Shape derived by FIp_RunFinish. Native/global domains remain distinct; not removed by helper or installation theorems.'
  if leaf in ['L142','L143','L144','L145','L146']:
   r['blocker']=r.get('blocker','')+' FIp concrete op17/op20/equality and semantic mask/add/mul/fromFn are installed. Full source-to-literal operands, canonicality and semantic terminal join remain.'
  if rid in ['L133','L134','L135','L136','L137','L138','L147']:
   r['blocker']='Retained in the SAME native returned continuation. FIp removes only the already-absent global copies. Carry SAME native Shape/read ranges/polynomials and saved weights through the continuation; instantiated quarter semantics must also be consumed. No removal credit.'
  if rid=='L159':r['blocker']='F3T_Runtime.StoredCarrierBinding remains at FIp_Install.configuration on SAME source/prover/runtime. Conditional fixture binding is not arbitrary deployed runtime association.'
  if rid=='L166':
   r['meaning']='Accepted-path source Result/effects association; both rejected prefixes reject and every earlier oracle read is counted, under the owner-approved success-conditioned ruling.'
   r['blocker']='Owner ruling is success-conditioned source Result/effects equality plus both-reject and counted issued reads on every rejected prefix. Known Parse-versus-panic discrepancy is recorded against D188, not counted as closure.'
  if rid=='L188':r['blocker']='Final source/object/tool/runtime/trust/axioms audit must follow the final coherent RPz3_ replay; focused checks cannot close it.'
 rows.append(r)
assert native_ids|global_ids <= {r['id'] for r in rows}
def tally(rs):
 return dict(rows=len(rs),classes={c:sum(r['classification']==c for r in rs) for c in ['T','P','G','C']},by_owner={o:{c:sum(r['classification']==c and r['owner']==o for r in rs) for c in ['T','P','G','C']} for o in ['lead','session A','external']})
def scopes(rs):
 return {s:tally([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}|{'deduplicated actual plus non-alias deployment':tally([r for r in rs if r['scope']!='deployment alias'])}
raw=scopes(rows);counts=scopes([r for r in rows if r['id']!='L137'])
assert counts==base['counts'] and raw==base['raw_counts']
assert counts['deduplicated actual plus non-alias deployment']['classes']==dict(T=89,P=22,G=13,C=0)
diff=[dict(id=r['id'],change='retained',classification=r['classification'],owner=r['owner'],scope=r['scope'],old_definition=next(x for x in base['rows'] if x['id']==r['id']).get('definition'),new_definition=r.get('definition')) for r in rows]
result=dict(actual_theorem='AspisR1.Rc9_Top.deployed',baseline='AspisR1.Rc8_Top.deployed',method=base['method'],baseline_sha256=sha(basefile),counts=counts,raw_counts=raw,distinct_delta=dict(T=0,P=0,G=0,C=0),raw_nonalias_delta=dict(T=0,P=0,G=0,C=0),removed=[],added=[],rows=rows,diff=diff,aliases={'L137':'L134','L185':'L159'},fixture_gate={'job':'JFs_','status':'OPEN; independent joint inhabitation gate, no fictional extra premise'},native_removals=[],global_removals=[],guard_change='FGm owners -> FIp owners with SAME-witness Shape guard internally derived; old owners imply new. No leaf-family removal.',dictionary_change='FIp concrete query/equality/semantic arithmetic/fromFn selected; finish unchanged; Rc9_Install.compatible and finish_preserved.',nonvacuity='Rc9_Nonvacuity.composed conditional SAME-cut accepted source/runtime executions and positive margin; Rc9_Clean.exists_world non-universal charged event; JFs_ remains OPEN')
(E/'Rc9_premises.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# Rc9 fresh mechanical recount','','Actual root: `AspisR1.Rc9_Top.deployed`. Ledger identities/guards/shared witnesses are preserved. Source-global and native-local domains remain distinct. Before and after full kernel statements: Rc9_BEFORE/AFTER.lean.txt. All totals match Rc8; delta **0T/0P/0G/0C**.','','| Basis | T | P | G | C |','|---|---:|---:|---:|---:|']
for label,data in [('Raw actual',raw['actual antecedent']),('Raw deployment',raw['deployment only']),('Raw non-alias combined',raw['deduplicated actual plus non-alias deployment']),('Distinct actual',counts['actual antecedent']),('Distinct non-alias combined',counts['deduplicated actual plus non-alias deployment'])]:
 c=data['classes'];lines.append(f"| {label} | {c['T']} | {c['P']} | {c['G']} | {c['C']} |")
lines+=['','Raw L185 is the L159 deployment alias; L137 duplicates L134 quarter. Native/global copies never alias.','','| Owner, distinct combined | T | P | G |','|---|---:|---:|---:|']
for owner,c in counts['deduplicated actual plus non-alias deployment']['by_owner'].items():lines.append(f"| {owner} | {c['T']} | {c['P']} | {c['G']} |")
lines+=['','| Every remaining P row | Scope | Owner | Covering job |','|---|---|---|---|']
for r in rows:
 if r['classification']=='P':lines.append(f"| {r['id']} | {r['scope']} | {r['owner']} | {r['running_job']} |")
lines+=['','JFs_ covers the separate OPEN joint fixture gate. L188 awaits the final replay and audit. Covering jobs are assignments only.','','FIp L133–L138/L147 global discharges are already present in Rc8. Every native-local copy remains; seven extra removals would be double counting. FIp installs more concrete source operations and weakens the five global owner law domains with an internally derived Shape guard; this is recorded precisely but yields no ledger leaf removal. Dictionary specialization does not establish the free terminal or full Pair/matching/semantic joins. No new trust, game restriction, failure event, numeric constant or cryptographic assumption was added.','','Rc9_Nonvacuity.composed invokes THIS root under SAME accepted native cuts and snapshots, yielding source/runtime acceptance and positive margin. Retained assumptions remain conditional; joint release inhabitation is OPEN.']
(E/'Rc9_LEDGER.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'counts':counts,'removed':[],'delta':result['distinct_delta']},indent=2))
