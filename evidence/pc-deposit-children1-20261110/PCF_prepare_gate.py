"""Prepare exact import expectations and raw roots; never infer credit here."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
expected={x['module']:x['imports'] for x in map(json.loads,(E.parent/'ledger23-20261110/NLS_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for x in map(json.loads,(E.parent/'pc-helpers1-20261110/PCB_EXPECTED_IMPORTS.jsonl').read_text().splitlines()):expected.setdefault(x['module'],x['imports'])
for folder,prefixes in [(E.parent/'sdk-borrow-20261109',('NLF_',)),(E.parent/'pc-deposit-pilot-20261110',('PCA_',)),(E,('PCF_',))]:
 for p in folder.glob('*.lean'):
  if not p.name.startswith(prefixes):continue
  names=['Init']+sum((s[7:].split() for s in p.read_text().splitlines() if s.startswith('import ')),[])
  expected[p.name[:-5]]=list(dict.fromkeys(names))
(E/'PCF_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps({'module':m,'imports':v})+'\n' for m,v in sorted(expected.items())))
own=['PCF_Count.'+n for n in ['complete','admitted_count','fewer','extra','result_state_effects']]
own+=['PCF_AccountLaws.payer','PCF_AccountLaws.token','PCF_LaneShape.complete','PCF_LaneValue.low_lane','PCF_ChildLaws.scanner','PCF_ChildLaws.first','PCF_Payer.result_state_effects','PCF_Token.result_state_effects']
pcb=json.loads((E.parent/'pc-helpers1-20261110/PCB_L045/sources/PCB_AUDIT_ROOTS.json').read_text())['roots']
nlf=json.loads((E.parent/'sdk-borrow-20261109/NLF_AUDIT_ROOTS.json').read_text())['groups']
nlf=list(dict.fromkeys(r for group in nlf for r in group))
roots=list(dict.fromkeys(['AspisR1.RPx_Deployed.deployed']+pcb+nlf+own))
(E/'PCF_ALL_AUDIT_ROOTS.json').write_text(json.dumps({'roots':roots,'own':own,'base':'ledger23 canonical closure/source hashes and accepted raw baseline retained; all new roots/headline/NLF/accepted PCB inspected in fresh combined environment'},indent=1)+'\n')
# Keep proof0 small enough to identify a failure without rerunning a timed-out aggregate.
batches=[roots[i:i+20] for i in range(0,len(roots),20)]
p=E/'PCF_TASKS.json';t=json.loads(p.read_text())
t['PCF_L027']={'kind':'audit','target':'NFX whole combined import scan','command':['PCF_native/PCF_AuditDriver','scan'],'files':{'PCF_EXPECTED_IMPORTS.jsonl':'PCF_EXPECTED_IMPORTS.jsonl','PCF_AUDIT_ROOTS.json':'PCF_ALL_AUDIT_ROOTS.json'},'collect':['PCF_LOADED_scan.jsonl'],'expected_time':'One canonical owner/declaration/import scan of the exact loaded combined closure'}
for i,b in enumerate(batches):
 n=f'PCF_ROOTS_{i:02}.json';(E/n).write_text(json.dumps({'roots':b},indent=1)+'\n');a=f'PCF_L{28+i:03}'
 t[a]={'kind':'audit','target':f'Raw NEP ax2 all roots batch {i}','command':['PCF_native/PCF_AuditDriver',f'proof{i}'],'files':{'PCF_AUDIT_ROOTS.json':n},'expected_time':'Exact raw ax2 traversal of the named root batch; same unchanged NEP walker and same PCF binary as eight fixtures'}
p.write_text(json.dumps(t,indent=1)+'\n')
(E/'PCF_GATE_PLAN.json').write_text(json.dumps({'combined':'PCF_L020','driver':'PCF_L021','link':'PCF_L022','fixtures':'PCF_L023','scan':'PCF_L027','raw_batches':[f'PCF_L{28+i:03}' for i in range(len(batches))],'own_roots':own,'total_roots':len(roots),'baseline_audit_reuse':'NLS exact pinned closure and its existing raw audit; no unchanged full verifier regression is rerun','walker_sha256':hashlib.sha256((E/'PCF_WALKER.c').read_bytes()).hexdigest(),'collector_disagreements':'Record under (ab\')(3); accepted only when raw axiom set is standard, never pad theorem axioms or weaken walker'},indent=1)+'\n')
print('PCF gate prepared:',len(roots),'roots in',len(batches),'batches; scan and eight fixtures mandatory')
