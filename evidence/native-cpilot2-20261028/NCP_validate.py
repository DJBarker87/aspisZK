from pathlib import Path
import json,re,hashlib,subprocess,shutil
E=Path(__file__).resolve().parent
for p in E.rglob('__pycache__'):shutil.rmtree(p)
receipts=[json.loads(p.read_text()) for p in E.glob('NCP_*/receipt.json')]
ks=[x for x in receipts if x['kind']=='kani'];ls=[x for x in receipts if x['kind']=='lean'];xs=[x for x in receipts if x['kind']=='extraction']
assert len(ks)==70 and len(ls)==59 and len(xs)==4
assert sorted(x['attempt'] for x in ks)==[f'NCP_K{i:03}' for i in range(1,71)]
expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for x in receipts:assert x['limits']==expected,x['attempt']
for p in E.glob('NCP_K*-graph.json'):
 x=json.loads(p.read_text());assert x['graph_matches_frozen'] and x['lock_unchanged']
for p in E.glob('*admission-*.json'):
 x=json.loads(p.read_text())
 if 'reservation' in x:assert x['exit']==0 and x['reservation']['allowed'] is True,p
 else:assert x['allowed'] is True,p
for p in E.glob('NCP_L*-reservation.json'):assert json.loads(p.read_text())['allowed'] is True,p
last={}
for x in sorted(ls,key=lambda x:x['attempt']):
 if x['exit_status']==0:last[x['module']]=x
sources=[p for p in Path('lean').rglob('*.lean') if p.parts[1].startswith('NCP_')]
checks={}
for p in sources:
 module=str(p.relative_to('lean')).removesuffix('.lean').replace('/','.')
 assert module in last,(module,'no passing receipt')
 x=last[module];key='NCP_generated/'+str(p.relative_to('lean'));sha=hashlib.sha256(p.read_bytes()).hexdigest();assert x['source_hashes'][key]==sha,(module,'source differs from last pass')
 assert not re.search(r'^\s*(?:axiom\b|opaque\b)|\bsorry\b|\badmit\b|\bnative_decide\b',p.read_text(),re.M),p
 for line in x['print_axioms']:
  m=re.search(r'\[([^\]]*)\]',line)
  if m:assert set(z.strip() for z in m[1].split(',') if z.strip())<={'propext','Classical.choice','Quot.sound'},line
 checks[module]={'attempt':x['attempt'],'source_sha256':sha}
# Exactly one preflight charged slot never invoked Lean.
rows=[json.loads(s) for s in (E/'NCP_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rows)==len({x['attempt'] for x in rows})==204
pre=next(x for x in rows if x['attempt']=='NCP_L036');assert pre['lean_invoked'] is False
assert subprocess.run(['git','diff','--exit-code','86fc5f0c2b^','HEAD','--','crates','programs'],capture_output=True).returncode==0
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
assert not [p for p in E.rglob('*') if p.is_file() and p.suffix in ['.olean','.pyc','.so','.o','.elf','.rlib']]
assert subprocess.run(['git','diff','--check'],capture_output=True).returncode==0
x={'status':'PASS','kani_runs':70,'lean_slots_charged':60,'lean_invocations':59,'lean_preflight_no_invocation':'NCP_L036','extractor_scopes':4,'all_70_frozen_graph_lock_checks':True,'all_caps':expected,'active_lean_sources':checks,'accepted_axioms_subset':['propext','Classical.choice','Quot.sound'],'shipped_source_diff':'none','file_limit_bytes':20*1024*1024,'no_committed_build_artifacts':True,'no_new_run_authorized':'both budgets exhausted','all_receipt_rows':len(rows)}
(E/'NCP_VALIDATION.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:v for k,v in x.items() if k!='active_lean_sources'},indent=2))
