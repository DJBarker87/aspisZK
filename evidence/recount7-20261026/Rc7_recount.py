"""Fresh kernel-statement/expanded-family recount. Shared witnesses, guards and
installation slots are deduplicated; native-local and global finish families
are distinct quantified obligations. Output evidence is never a premise.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
old=load(R/'evidence/recount6-20261026/Rc6_premises.json')
fgl=load(R/'evidence/finish-global-20261026/FGl_premises.json')
plan=load(E/'Rc7_audit_plan.json');logs={};catalog={};audit=[]
for a in plan:
 p=E/a['attempt'];rec=load(p/'receipt.json');assert rec['exit_status']==0,a
 assert rec['source_hashes'][a['module']+'.lean']==sha(R/'lean'/(a['module']+'.lean'))
 s=(p/'stdout.log').read_text();assert not re.search(r'\berror(?:\(|:)',s),a
 logs[a['module']]=s;audit.append(dict(**a,stdout_sha256=sha(p/'stdout.log'),source_sha256=sha(R/'lean'/(a['module']+'.lean'))))
 for b in re.split(r'(?=^structure )',s,flags=re.M):
  if not b.startswith('structure ') or 'fields:\n' not in b:continue
  key=re.match(r'structure (\S+)',b)[1];fields=b.split('fields:\n',1)[1].split('constructor:',1)[0]
  catalog[key]=dict(fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
comp=logs['Rc7_AuditRoot']
def statement(name):
 a=comp.index('@AspisR1.'+name+' :');b=comp.find('\n@AspisR1.',a+1)
 return comp[a:b if b>=0 else len(comp)].split("\n'AspisR1.",1)[0].rstrip()+'\n'
for name,label in [('Rc6_Top.deployed','BEFORE'),('P2P_Top.deployed','P2P_BEFORE'),('FGl_Headline.deployed','FGL_BEFORE'),('Rc7_Top.deployed','AFTER'),('Rc7_Nonvacuity.composed','NONVACUITY'),('Rc7_Reverse.same_witnesses','REVERSE')]:
 (E/('Rc7_'+label+'.lean.txt')).write_text(statement(name))
root=statement('Rc7_Top.deployed')
for x in ['P2P_Result.Outcome','FGl_PreparedAt.Owners','F3T_Runtime.StoredCarrierBinding','CPH_Game.DeployedPairExecution','CPR_DataPersistence.TwoTransactionLaw','F3Y_SourceClaims.Claims','F3Y_AccountMass.Claims','F3X_Account.program','P2P_NativeSelection.pair','2965']:
 assert x in root,x
for x in ['F3T_CanonicalJoin.AcceptedVerifierJoin','chooseSecond','prefixBound','choiceBound','F3Y_PreparedAt.Owners']:
 assert x not in root,x
# Retained global groups expand to 7 pairing + 1 matches + 3 semantic + 1 dot.
globaldefs=logs['Rc7_AuditGlobalOwners']
assert len(catalog['AspisR1.FGl_FinishLeaves.PairingRemaining']['field_names'])==3
assert len(catalog['AspisR1.Port4D_Pairing.RoundLaws']['field_names'])==3
equations=globaldefs.split('def AspisR1.R3SemanticEquationCore.Equations',1)[1]
assert equations.count(' ∧')==2 and 'Fin 9' in equations and 'alpha 9' in equations
assert 'FGl_FinishLeaves.Holds' in globaldefs
assert 'sourceE' not in globaldefs.split('def AspisR1.FGl_FinishLeaves.Holds',1)[1].split('structure AspisR1.FGl_FinishLeaves.PairingRemaining',1)[0]
# Crosscheck independently elaborated inherited records against predecessor output.
shared={}
for file in ['evidence/recount6-20261026/Rc6_field_catalog.json','evidence/finish-global-20261026/FGl_field_catalog.json']:
 prev=load(R/file);same=[]
 for k in prev.keys() & catalog.keys():
  assert prev[k]['fields']==catalog[k]['fields'],('changed inherited structure',file,k)
  same.append(k)
 shared[file]=sorted(same)
assert len(shared['evidence/recount6-20261026/Rc6_field_catalog.json'])>=30
# Source derivation check supplements (does not replace) kernel statements.
top=(R/'lean/Rc7_Top.lean').read_text()
for x in ['Rc7_Native.accepted','P2P_R6Result.strengthen','P2P_Release.remove','FGl_Bound.bound','FGl_Cost.source_cost','F3Y_AccountMass.budget']:
 assert x in top,x
assert 'P2P_Top.deployed' not in top and 'FGl_Headline.deployed' not in top
for x in ['PFin_Packet.Facts','P6C_FullBoundary.Facts','P2P_Origin.Fact','bad ∨']:
 assert x in (R/'lean/P2P_Result.lean').read_text(),x
citation='docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md#owner-approved-amendment-2026-10-26 (items 1–3; especially two-transaction game a–d), owner instruction 2026-10-26: eleven game clauses and L083/L084 are class G'
game={'L083','L084'}|{f'Rc5_G{i:03}' for i in range(1,12)}
retire={
'L165':dict(theorem='PFin_Packet.from_cut / P2P_R6Result.strengthen / Rc7_Top.deployed',reason='Derived packet on the SAME native cuts supplies physical/stored bytes, full parseReached, Aligned, query/data decoding and SessionAPrepare. Header-only to full parser/semantic-transcript source association is closed. Global finish arithmetic remains separately counted.'),
'L179':dict(theorem='NP6_ParsedPair.accepted_pair_unified / NP6_ResultBridge.complete_result',reason='Native P6 concrete std/source/Result/frame/ownership/cleanup certificate for NP6_StdModel.calls, already the selected Rc5/Rc6/Rc7 dictionary. Retained extraction/runtime/SDK/Allocator hypotheses are unchanged.',evidence='evidence/native-p6-20261026/NP6_SOURCE_CERTIFICATE.md; Rc7_inherited_evidence.json'),
'L186':dict(theorem='No new Lean theorem: Low2_source_to_elf_manifest + 140 S10 checks under retained P7',reason='lowering2 reproduces all three frozen ELFs and validates exact source/order correspondence; retained P7, no widened trust.',evidence='evidence/lowering2-20261026/Low2_final_receipt.json; Rc7_inherited_evidence.json')}
removed_binding={'L097','L098'}
rows=[]
for raw in fgl['rows']:
 r=copy.deepcopy(raw);i=r['id']
 if i in removed_binding or i in retire:continue
 if i in game:r.update(classification='G',role='owner-approved experiment definition',classification_citation=citation,fixture_job='JFw_')
 if r['classification']=='P':
  if i in {'L159','L185'}:job='SCE_'
  elif i=='L166':job='BEf_'
  elif i.startswith('F3Y_G_') or (r['owner']=='session A' and r['scope']=='actual antecedent'):job='FIn_'
  else:job='UNCOVERED'
  r['running_job']=job
 r['status']='retained';r['evidence']='Rc7 fresh kernel inventories009–060; checked native same-cut strengthening001–008'
 if i=='L181':r['blocker']='Retained residual: FGl_Join.accepted_raw_join_or_collision establishes accepted-source complete ordered log/result OR the charged event; it does not prove rejected-source/native/runtime query-prefix transport for the complete deployed experiment. No obsolete frozen2 exact join is required. Accepted portion is closed; global rejected-prefix/source association is not.'
 if i=='L176':r['blocker']='Separate S6 native decoded/public transport to the adopted implementation remains; parser/output equations are not all native carrier/source interpretation.'
 if i=='L187':r['blocker']='Final coherent frozen dependency replay is not performed by focused cached inventories.'
 if i=='L188':r['blocker']='Release-wide trust/axiom audit remains; standard axioms on this top alone do not close it.'
 rows.append(r)
assert {r['id'] for r in rows if r['classification']=='G'}==game
by={r['id']:r for r in rows};before={r['id']:r for r in old['rows']}
removed=set(before)-set(by);added=set(by)-set(before)
assert removed=={'L097','L098','L157','N117','N118','L165','L179','L182','L186'},removed
assert added=={f'F3Y_G_L{i}' for i in [133,134,135,136,137,138,142,143,144,145,146,147]},added
reason={
'L097':'P2P_Release.remove on the same F3X account/selector; byte proof binding OR single charged event',
'L098':'P2P_Release.remove on the same F3X account/selector; byte public binding OR same event',
'L157':'FGl_Join.accepted_raw_join_or_collision / FGl_Bound.bound; supplied raw canonicality replaced by charged complete log/result equality',
'N117':'Independent account adversary eliminated: F3X_Account is constructed from the headline byte prover; F3Y_AccountMass.budget derives its reads',
'N118':'Independent chooseSecond eliminated with arbitrary account adversary; no unproved source/account coupling guard added',
'L182':'Alias of removed raw L157; retired with zero additional deduplicated credit',
**{k:v['reason'] for k,v in retire.items()}}
diff=[]
for i,o in before.items():
 if i in removed:diff.append(dict(**o,change='removed',reason=reason[i],closure=retire.get(i)))
 elif i in game:diff.append(dict(**by[i],change='P to G',before_classification=o['classification'],reason=citation))
 else:diff.append(dict(**by[i],change='retained'))
for i in sorted(added):diff.append(dict(**by[i],change='added global family',reason='FGl global world/submission/Evidence quantifiers differ from native-local continuation. No bundling/dedup discount.'))
def counts(rs):
 return dict(rows=len(rs),classes={c:sum(r['classification']==c for r in rs) for c in ['T','P','G','C']},by_owner={o:{c:sum(r['classification']==c and r['owner']==o for r in rs) for c in ['T','P','G','C']} for o in ['lead','session A','external']})
def summary(rs):
 d={s:counts([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
 d['all retained audit rows']=counts(rs);d['deduplicated actual plus non-alias deployment']=counts([r for r in rs if r['scope']!='deployment alias']);return d
adjusted=copy.deepcopy(old['rows'])
for r in adjusted:
 if r['id'] in game:r['classification']='G'
cs=summary(rows);bs=summary(adjusted)
assert cs['actual antecedent']['classes']==dict(T=83,P=26,G=13,C=0),cs
assert cs['deduplicated actual plus non-alias deployment']['classes']==dict(T=89,P=31,G=13,C=0),cs
result=dict(actual_theorem='AspisR1.Rc7_Top.deployed',baseline=old['actual_theorem'],method=__doc__,classification_citation=citation,counts=cs,before_counts_historical=old['counts'],before_counts_same_class_G=bs,rows=rows,diff=diff,removed_rows=sorted(removed),added_rows=sorted(added),reclassified_G=sorted(game),deployment_retirements=retire,statement_evidence=audit,unchanged_fresh_structure_inventories=shared,remaining_P_by_running_job=dict(Counter(r['running_job'] for r in rows if r['classification']=='P')),delta=dict(actual_P_removed=5,actual_P_global_added=12,actual_P_net_same_classification=7,deployment_P_removed=3,alias_removed_no_extra_credit=1,deduplicated_P_net_same_classification=4,T=0,C=0),caveat='Reclassification is not proof discharge. Charged binding and raw join alter conclusions; global laws add quantified obligations. No unconditional reverse of old raw/exact-cost top. Same native witnesses and clean-branch reverse are proved. Full release non-vacuity/replay remain open.')
(E/'Rc7_premises.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
(E/'Rc7_field_catalog.json').write_text(json.dumps(catalog,indent=2,ensure_ascii=False)+'\n')
lines=['# Rc7 remaining rows','','Covering job is not closure. FIn_ covers native-local and world-global finish families separately. JFw_ is the joint-fixture job; all 13 game-domain rows are class G and listed separately.','','| ID | Class | Owner | Scope | Job | Family |','|---|---|---|---|---|---|']
for r in rows:
 if r['classification']=='P':lines.append('| '+' | '.join(str(r[k]) for k in ['id','classification','owner','scope','running_job','name'])+' |')
lines+=['','## Owner-approved game definitions (class G)','','Citation: '+citation,'','| ID | Name | Fixture job |','|---|---|---|']
for r in rows:
 if r['classification']=='G':lines.append(f"| {r['id']} | {r['name']} | JFw_ |")
(E/'Rc7_REMAINING.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(counts=cs,removed=sorted(removed),added=sorted(added),coverage=result['remaining_P_by_running_job']),indent=2))
