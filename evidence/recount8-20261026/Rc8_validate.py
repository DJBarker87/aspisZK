"""Validate Rc8 source/receipt correspondence and append-only document integrity."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path(__file__).resolve().parent; R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[];audits=[]
for p in sorted(E.glob('Rc8_[0-9][0-9][0-9]/receipt.json')):
 j=json.loads(p.read_text())
 assert j['exit_status']==0,(p,j['exit_status'])
 assert j['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},p
 assert '-M7000' in j['command'] and int(j['swaps'])==0,p
 assert j['source_revision'] and j['deps_fingerprint']['selected_objects'],p
 for name,digest in j['source_hashes'].items():
  assert name.startswith('Rc8_'),name
  assert sha(R/'lean'/name)==digest,(name,p)
  assert sha(p.parent/'sources'/name)==digest,(name,p)
 for line in j['print_axioms']:
  if 'depends on axioms:' in line:
   values=line.split('depends on axioms:',1)[1].strip().strip('[]').split(', ')
   assert set(values)<={'propext','Classical.choice','Quot.sound'},(p,line)
  assert 'sorryAx' not in line,line
 audits+=j['print_axioms']
 receipts.append({k:j[k] for k in ['attempt','sources','source_revision','source_tree_dirty','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']}|{'receipt_sha256':sha(p),'deps_fingerprint_sha256':hashlib.sha256(json.dumps(j['deps_fingerprint'],sort_keys=True).encode()).hexdigest()})
for p in R.joinpath('lean').glob('Rc8_*.lean'):
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|set_option (maxRecDepth|maxHeartbeats)',s),p
 assert not re.search(r'^\s*axiom\s',s,re.M),p
 assert any(p.name in j['sources'] for j in receipts),('unchecked module',p)
 theorem_names=re.findall(r'^theorem\s+(\w+)',s,re.M)
 ns=re.search(r'^namespace\s+(\S+)',s,re.M)
 for name in theorem_names:
  full=ns[1]+'.'+name
  assert any("'"+full+"'" in x for x in audits),('missing axioms',full)
pins=json.loads(E.joinpath('Rc8_input-pins.json').read_text())
append_integrity={}
for filename,pin in pins['append_only_inputs'].items():
 data=R.joinpath(filename).read_bytes();n=pin['bytes']
 assert hashlib.sha256(data[:n]).hexdigest()==pin['sha256'],filename
 append_integrity[filename]={'prefix_bytes':n,'prefix_sha256':pin['sha256'],'current_sha256':sha(R/filename),'appended_bytes':len(data)-n}
if '--final' in sys.argv:
 assert len(receipts)==60,len(receipts)
 assert [j['attempt'] for j in receipts]==[f'Rc8_{n:03}' for n in range(1,61)]
 assert all(v['appended_bytes']>0 for v in append_integrity.values())
assert subprocess.run(['git','diff','--check',pins['revision']],cwd=R,capture_output=True).returncode==0
result={'Lean_attempts':len(receipts),'Kani_runs':0,'all_exit_zero':True,'all_standard_axioms':True,'one_scope_at_a_time':'task calls strictly serial; existing host reservation for every attempt','caps':'6G/8G/swap0/64, -M7000','append_integrity':append_integrity,'receipts':receipts,'top_source_sha256':sha(R/'lean/Rc8_Top.lean')}
E.joinpath('Rc8_validation.json').write_text(json.dumps(result,indent=2)+'\n')
E.joinpath('Rc8_attempts.jsonl').write_text(''.join(json.dumps(j)+'\n' for j in receipts))
print(json.dumps({'Lean':len(receipts),'Kani':0,'all_passed':True,'max_RSS_KiB':max(int(j['peak_rss_kib']) for j in receipts),'sum_wall_seconds':sum(j['wall_seconds'] for j in receipts)},indent=2))
