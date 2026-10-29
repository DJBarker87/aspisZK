"""Proposed local overlay; never writes the authoritative NCZ packet."""
from pathlib import Path
import sys,json,hashlib,collections,importlib.util,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
base=json.loads((R/'evidence/native-front1-20261028/NDD_LEDGER.json').read_text())
delta=json.loads((E/'NDL_LEDGER_DELTA.json').read_text());accepted=[r for r in delta['members'] if r['status']=='CLOSED-local' and r.get('lean_attempt','').startswith('NDL_')]
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
def pin(p):
 q=R/p;b=q.read_bytes();base['evidence_manifest'][p]=dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),revision=revision,git_blob=None,source='NDL candidate worktree overlay; not adopted by NCZ snapshot')
def ep(n):return str((E/n).relative_to(R))
for c in accepted:
 ident='NDL::'+c['function'];receipts=[str(Path('evidence/native-front1b-20261028' if a.startswith('NDL_') else 'evidence/native-front1-20261028')/a/'receipt.json') for a in [c['lean_attempt'],c['kani_attempt'],c['negative_control'],c['extraction']]]
 evidence=[ep('NDL_FRONTIER_BRIDGES.md'),ep('NDL_LEDGER_DELTA.json')]+receipts
 for p in evidence:pin(p)
 hypotheses=[dict(name=ident+'.PacketDomain',statement=c['domain']+'; exact same typed inputs and Result/value interpretation in '+c['lean_theorem'],discharged_by=None),dict(name=ident+'.PhysicalInterpretation',statement='Pinned native/reference/cohort type encoding, tool semantic transport, standard library/runtime/ABI and artifact correspondence qualifications remain retained.',discharged_by=None)]
 claim=dict(claim_id=ident,function=c['function'],admissible_local_credit=True,quarantined_support=[],feature_parity='PINNED FROZEN BODY; deployed verifier features in NDD_K039/040 graph receipts',reported_status='CLOSED local',medium='P6 hybrid',audit_id=c['kani_attempt'],profile='NDL guard SAME-record association',limitations=['Local value/Result bridge only; every caller domain and physical interpretation remains OPEN'],named_hypotheses=hypotheses,evidence=evidence,receipts=receipts,source_claim_text=[json.dumps(c,sort_keys=True)],arithmetic_stubs=[],stub_attributes=[],replaced_quarantined_support=[],composition_trust=delta['trust_change'])
 base['claims'].append(claim)
 for row in base['rows']:
  if row['function']!=c['function']:continue
  row['bridge_status']='CLOSED-CONDITIONAL';row['selected_claims']=[ident];row['claim_ids']=sorted(set(row['claim_ids']+[ident]));row['named_hypotheses']=hypotheses
  row['medium']=sorted(set(row['medium']+['P6 hybrid']))
  row['feature_parity_summary']='NDL exact frozen body and inherited deployed verifier feature parity; caller/runtime limits retained'
  row['feature_parity'].append(dict(claim=ident,status=claim['feature_parity']))
  row['evidence']=sorted(set(row['evidence']+evidence));row['receipts']=sorted(set(row['receipts']+receipts))
  row['receipt_sha256'].update({p:base['evidence_manifest'][p]['sha256'] for p in receipts});row['no_credit_reason']=None
functions=collections.defaultdict(list)
for row in base['rows']:functions[row['function']].append(row)
claims=collections.defaultdict(list)
for c in base['claims']:claims[c['function']].append(c)
status={n:('CLOSED-CONDITIONAL' if any(c['admissible_local_credit'] for c in claims[n]) else 'quarantined' if claims[n] and all(c['quarantined_support'] for c in claims[n]) else 'OPEN') for n in functions}
graph={n:set(t for r in rows for t in r['canonical_callees']) for n,rows in functions.items()};reverse={n:set() for n in graph}
for caller,targets in graph.items():
 for t in targets:reverse[t].add(caller)
def reach(n,edges):
 seen=set();todo=list(edges[n])
 while todo:
  x=todo.pop()
  if x not in seen:seen.add(x);todo.extend(edges[x])
 return seen-{n}
down={n:reach(n,graph) for n in graph};up={n:reach(n,reverse) for n in graph}
components=[];assigned=set()
for n in sorted(graph):
 if n not in assigned:g={n}|(down[n]&up[n]);components.append(sorted(g));assigned.update(g)
component={n:i for i,g in enumerate(components) for n in g};opens={n for n,v in status.items() if v in ['OPEN','quarantined']};frontier=[]
for i in sorted({component[n] for n in opens}):
 g=components[i]
 if {component[t] for t in down[g[0]] if t in opens}-{i}:continue
 candidates=sorted(set(g)&opens);n=sorted(candidates,key=lambda n:(-len(up[n]),n))[0]
 frontier.append(dict(representative=n,open_scc_members=candidates,all_scc_members=g,dependent_functions=len(up[n]),dependent_rows=sum(len(functions[x]) for x in up[n])))
frontier.sort(key=lambda x:(-x['dependent_rows'],x['representative']))
assert all(any(t['representative']==n or t['representative'] in down[n] for t in frontier) for n in opens)
for r in base['rows']:
 r['open_transitive_dependencies']=sorted(down[r['function']]&opens)
 for o in r['caller_domain_obligations']:
  if 'callee' in o:
   n=o['callee'];o['callee_local_status']=status[n];o['callee_claims']=[c['claim_id'] for c in claims[n] if c['admissible_local_credit']];o['required_named_hypotheses']=sorted({h['name'] for c in claims[n] if c['admissible_local_credit'] for h in c['named_hypotheses']})
for tx in ['TX1','TX2','all_rows']:
 chosen=[r for r in base['rows'] if tx=='all_rows' or r['transaction']==tx]
 base['coverage'][tx]['local_bridge_status']=dict(sorted(collections.Counter(r['bridge_status'] for r in chosen).items()))
base['coverage']['unique_functions']['local_bridge_status']=dict(sorted(collections.Counter(status.values()).items()))
base['critical_path']['frontier']=frontier
base['critical_path']['highest_impact_open']=[dict(function=n,dependent_functions=len(up[n]),dependent_rows=sum(len(functions[x]) for x in up[n])) for n in sorted(opens,key=lambda n:(-sum(len(functions[x]) for x in up[n]),n))[:20]]
base['NDL_candidate_overlay']=dict(status='PROPOSED; authoritative NCZ recomputation needs an explicit evidence-snapshot refresh',local_claims=len(accepted),newly_composed_rows=0,delta=ep('NDL_LEDGER_DELTA.json'))
base['budget']=dict(lean_used=delta['budget_used'].get('lean',0),lean_limit=80,kani_used=delta['budget_used'].get('kani',0),kani_limit=80,extraction_used=delta['budget_used'].get('extract',0),extraction_limit=20)
modpath=R/'evidence/native-compledger-20261028/NCZ_validate.py';spec=importlib.util.spec_from_file_location('NCZ_readonly',modpath);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.validate_invariants(base)
(E/'NDL_LEDGER.json').write_text(json.dumps(base,indent=2,sort_keys=True)+'\n')
result=dict(schema_invariants='PASS',source='unmodified NCZ.validate_invariants',proposed_local_claims=len(accepted),coverage=base['coverage'],frontier_representatives=len(frontier),new_composed_closures=0,authoritative_recompute='NOT accepted; run NCZ_validate.py on this copy and report snapshot refusal separately')
(E/'NDL_OVERLAY_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
