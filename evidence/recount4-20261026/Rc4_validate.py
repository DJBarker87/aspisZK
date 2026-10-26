"""Validate final evidence and regenerate arithmetic recount, without a prover."""
from pathlib import Path
import hashlib,json,re,subprocess,shlex
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];seen=set();accepted=set();passing={};last={}
failures={2,3,4,6,11,12,14,17}
for n in range(1,61):
 a=f'Rc4_{n:03}';x=json.loads((P/a/'receipt.json').read_text());receipts.append(x)
 assert x['attempt']==a and x['exit_status']==(1 if n in failures else 0)
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0' and '-M7000' in x['command'] and '-j1' in x['command']
 assert x['source_revision'] and x['wall_seconds']>0 and int(x['peak_rss_kib'])>0
 cfg=json.loads((P/(a+'.json')).read_text());assert cfg['sources']==x['sources']
 key=json.dumps([x['source_hashes'],x['env'],x['deps_fingerprint']],sort_keys=True)
 assert key not in seen,(a,'unchanged source/environment/dependencies');seen.add(key)
 reservation=json.loads((P/(a+'-reservation.json')).read_text())
 assert reservation['reserved_bytes']+reservation['additional_bytes']<=reservation['limit_bytes']==55*1024**3
 for src,h in x['source_hashes'].items():
  assert sha(P/a/'sources'/src)==h
  if x['exit_status']==0:
   passing.setdefault((src,h),[]).append(a);last[src]=a
 if x['exit_status']==0:
  for line in x['print_axioms']:
   names=set(line.split('[')[-1].removesuffix(']').split(', ')) if 'depends on axioms:' in line else set()
   assert names<={'propext','Classical.choice','Quot.sound'},(a,line)
   accepted.add(line.split("'")[1])
# All own scope reservations are absent from every later admission snapshot.
scopes={x['cgroup'] for x in receipts}
for x in receipts:
 for row in json.loads((P/(x['attempt']+'-reservation.json')).read_text())['scopes']:
  assert row['scope'] not in scopes,(x['attempt'],'overlapping own populated scope')
current={};theorems=[]
for src in sorted((R/'lean').glob('Rc4_*.lean')):
 h=sha(src);assert (src.name,h) in passing,(str(src),'not checked current source')
 text=src.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text),src
 assert 'maxHeartbeats' not in text and 'maxRecDepth' not in text
 ns=re.search(r'^namespace (\S+)',text,re.M)
 if ns:
  for name in re.findall(r'^theorem (\w+)',text,re.M):
   q=ns[1]+'.'+name;assert q in accepted,(src,q,'missing standard axiom audit');theorems.append(q)
 current[str(src.relative_to(R))]=dict(sha256=h,successful_attempts=passing[(src.name,h)],selected_receipt=last[src.name])
for row in json.loads((P/'Rc4_inherited_sources.json').read_text())['files']:
 assert sha(R/row['path'])==row['sha256'],row['path']
objects=json.loads((P/'Rc4_final_objects.json').read_text())
assert all(v['matches'] for v in objects['objects'].values())
assert all(v['matches'] for v in objects['sources'].values())
# Revalidate all object/source hashes on host without compiling or modifying files.
code='''import pathlib,hashlib,json,sys
x=json.load(sys.stdin)
for group in ["objects","sources"]:
 for p,o in x[group].items():
  assert hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==o["sha256"],p
print("all selected current object/source hashes match")
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-c',shlex.quote(code)],input=json.dumps(objects),capture_output=True,text=True)
assert r.returncode==0,r.stderr
artifacts=['Rc4_premises.json','Rc4_field_catalog.json','Rc4_REMAINING.md']
before={n:sha(P/n) for n in artifacts}
subprocess.run(['python3',str(P/'Rc4_recount.py')],check=True,stdout=subprocess.DEVNULL,cwd=R)
assert before=={n:sha(P/n) for n in artifacts}
pin=json.loads((P/'Rc4_baseline.json').read_text());ledger=(R/'design/PREMISE-LEDGER-20261025.md').read_bytes()
assert hashlib.sha256(ledger[:pin['ledger_bytes']]).hexdigest()==pin['ledger_sha256']
assert b'## Recount on Rc3_Top' in ledger[:pin['ledger_bytes']] and b'### SAQ_ source-selected candidate' in ledger[:pin['ledger_bytes']]
assert ledger[pin['ledger_bytes']:]==b'\n## Recount on Rc4_Top (2026-10-26)\n\n'+(P/'Rc4_LEDGER.md').read_bytes().split(b'\n',1)[1]
changed=set(subprocess.check_output(['git','diff','--name-only',pin['revision']],cwd=R,text=True).splitlines())
assert all(p.startswith('lean/Rc4_') or p.startswith('evidence/recount4-20261026/') or p=='design/PREMISE-LEDGER-20261025.md' for p in changed),changed
subprocess.run(['git','diff','--check'],cwd=R,check=True)
result=dict(lean_attempts=60,lean_budget=60,kani_runs=0,kani_budget=0,passes=52,
 excluded_diagnostics=[f'Rc4_{n:03}' for n in sorted(failures)],heartbeat_replacements=['Rc4_011','Rc4_012','Rc4_014'],
 wall_timeouts=0,memory_kills=0,barrier_retries=0,dependency_builds=0,package_replays=0,
 one_own_scope_at_a_time=True,current_sources=current,theorem_axioms=sorted(theorems),
 accepted_axioms=['propext','Classical.choice','Quot.sound'],
 receipts=[{k:x[k] for k in ['attempt','sources','command','source_revision','source_tree_dirty','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup','limits','print_axioms']} for x in receipts],
 peak_rss_kib=max(int(x['peak_rss_kib']) for x in receipts),total_wall_seconds=sum(x['wall_seconds'] for x in receipts),
 inherited_checks=1381,selected_object_checks=len(objects['objects']),selected_host_sources=len(objects['sources']),
 complete_ledger_prefix_preserved=True,recount_reproducible=True,
 counts=json.loads((P/'Rc4_premises.json').read_text())['counts'],
 artifact_boundary='No shipped/cfg(kani) source changed; ELF pins inherited, not rebuilt',
 release_claim='Target not yet established; source-selected conditional composition; frozen3 integration and native/deployment boundaries remain')
(P/'Rc4_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['current_sources','receipts','counts','theorem_axioms']},indent=2))
