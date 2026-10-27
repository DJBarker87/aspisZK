from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
records=[];accepted={}
for folder in sorted(P.glob('JGo_TX2_[0-9][0-9][0-9]')):
 r=json.loads((folder/'receipt.json').read_text());n=int(r['attempt'].rsplit('_',1)[1])
 log=(folder/'stdout.log').read_text();audits=[]
 for m in re.finditer(r"^'([^']+)' (?:depends on axioms: \[([\s\S]*?)\]|does not depend on any axioms)",log,re.M):
  axioms=[] if m.group(2) is None else [a.strip() for a in m.group(2).split(',')]
  audits.append({'declaration':m.group(1),'axioms':axioms,'full_print':m.group(0)})
 if r['exit_status']==0:
  assert audits,folder
  assert all(set(a['axioms'])<=allowed for a in audits),(folder,audits)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},folder
 assert '-M7000' in r['command'] and '-j1' in r['command'],folder
 assert r['env']['LEAN_PATH'].startswith('/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects:'),folder
 assert int(r['swaps'])==0,folder
 for f,h in r['source_hashes'].items():
  snapshot=(folder/'sources'/f).read_bytes();assert sha(snapshot)==h,(folder,f)
  if r['exit_status']==0:accepted.setdefault((f,h),[]).append(n)
 rec={'attempt':n,'module':r['sources'],'source_revision':r['source_revision'],
   'source_tree_dirty':r['source_tree_dirty'],'source_sha256':r['source_hashes'],
   'dependency_fingerprint_sha256':sha(json.dumps(r['deps_fingerprint'],sort_keys=True).encode()),
   'dependencies':r['deps_fingerprint'],'command':r['command'],'exit_status':r['exit_status'],
   'wall_seconds':r['wall_seconds'],'peak_rss_kib':int(r['peak_rss_kib']),'swaps':int(r['swaps']),
   'cgroup':r['cgroup'],'limits':r['limits'],'axiom_audits':audits,
   'kernel_memory_rejection':'excessive memory consumption' in log,
   'errors':[x for x in log.splitlines() if 'error' in x.lower() or 'exception' in x.lower()]}
 records.append(rec)
assert [r['attempt'] for r in records]==list(range(1,101)),[r['attempt'] for r in records]
(P/'JGo_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in records))
current=[]
for p in sorted((R/'lean').glob('JGo_*.lean')):
 h=sha(p.read_bytes());key=(p.name,h);assert key in accepted,('NO CURRENT-HASH ACCEPTED RECEIPT',p,h)
 text=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b',text),p
 assert not re.search(r'^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M),p
 for theorem in re.findall(r'^theorem\s+([\w\u0080-\uffff\']+)',text,re.M):
  assert '#print axioms '+theorem in text,(p,theorem)
 current.append({'module':p.name,'sha256':h,'accepted_attempts':accepted[key]})
(P/'JGo_VALIDATION.json').write_text(json.dumps(current,indent=2)+'\n')
before=(P/'JGo_BEFORE_ARX_Root.lean.txt').read_bytes();after=(R/'lean/ARX_Root.lean').read_bytes();assert before==after
(P/'JGo_AFTER_ARX_Root.lean.txt').write_bytes(after)
(P/'JGo_AFTER_ARX_KERNEL.txt').write_bytes((P/'JGo_TX2_100/stdout.log').read_bytes())
ledger=json.loads((P/'JGo_LEDGER_DELTA.json').read_text())
last=json.loads((P/'JGo_TX2_100/receipt.json').read_text())
ledger['selected_object_100']=last['deps_fingerprint']['selected_objects']['ARX_Root.olean']
assert ledger['selected_object_100']==ledger['selected_object_070']
(P/'JGo_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
summary={'attempts':100,'pass':sum(r['exit_status']==0 for r in records),'reject':sum(r['exit_status']!=0 for r in records),
 'kani_runs':0,'delivered_current_modules':len(current),'total_lean_wall_seconds':sum(r['wall_seconds'] for r in records),
 'max_peak_rss_kib':max(r['peak_rss_kib'] for r in records),'total_swaps':sum(r['swaps'] for r in records),
 'memory_rejections':[r['attempt'] for r in records if r['kernel_memory_rejection']],
 'final_audit':{k:records[-1][k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_tree_dirty']},
 'actual_top_sha256':sha(after),'actual_top_changed':False,'actual_premises_removed':0,
 'complete_accepted2':False,'complete_joint_nonvacuity':False,'hundred_bit_target_established':False}
(P/'JGo_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
entries=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name!='JGo_EVIDENCE_MANIFEST.json':
  assert p.suffix not in {'.olean','.ilean','.o','.so','.elf','.tar','.gz','.zip','.pyc'},p
  entries.append({'path':str(p.relative_to(R)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())})
(P/'JGo_EVIDENCE_MANIFEST.json').write_text(json.dumps(entries,indent=2)+'\n')
print(json.dumps(summary,indent=2))
