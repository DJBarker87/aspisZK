from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
receipts=[json.loads(p.read_text()) for p in sorted(P.glob('FJi_[0-9][0-9][0-9]/receipt.json'))]
assert len(receipts)<=100
allowed={'propext','Classical.choice','Quot.sound'}
accepted={};failed=[]
for r in receipts:
 assert all(k in r for k in ['attempt','sources','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup','limits','print_axioms'])
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command']
 if r['exit_status']!=0: failed.append(r['attempt']);continue
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   axioms=set(line.split('depends on axioms: [',1)[1].rstrip(']').split(', '))
   assert axioms<=allowed,(r['attempt'],line)
 for name,sha in r['source_hashes'].items(): accepted[(name,sha)]=r['attempt']
sources=[];unchecked=[]
for p in sorted((R/'lean').glob('FJi_*.lean')):
 s=p.read_text();sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxHeartbeats|maxRecDepth)\b',s),p
 a=accepted.get((p.name,sha))
 if not a:unchecked.append(p.name)
 sources.append({'path':str(p.relative_to(R)),'sha256':sha,'passing_exact_source_attempt':a})
start=receipts[0]['source_revision']
changes=subprocess.check_output(['git','diff','--name-only',start],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/FJi_') or p.startswith('evidence/finish-match1-20261027/') for p in changes),changes
x={'lean_attempts':len(receipts),'kani_runs':0,'successes':len(receipts)-len(failed),'failed':failed,'sources':sources,'unchecked':unchecked,'peak_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'swaps':sum(int(r['swaps']) for r in receipts),'all_successful_axioms_standard':True,'protected_file_changes':[],'source_start_revision':start,'actual_top_removed':[],'final_manifest_replay':False,'shipped_file_changes':False,'ELF_rebuild_triggered':False}
audit=next((r for r in receipts if r['attempt']=='FJi_100'),None)
if audit:
 x['final_axioms_audit']={'attempt':'FJi_100','exit_status':audit['exit_status'],'printed_targets':len(audit['print_axioms'])}
(P/'FJi_validation.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:v for k,v in x.items() if k!='sources'},indent=2))
if '--final' in __import__('sys').argv:
 assert len(receipts)==100
 assert not unchecked,unchecked
