import hashlib,json,re,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent
receipts=[]
for n in range(1,101):
 p=root/f'Hist_{n:03}'/'receipt.json'
 if p.exists():
  d=json.loads(p.read_text());receipts.append(d)
assert len(receipts)==97
assert {n for n in range(1,101) if not (root/f'Hist_{n:03}'/'receipt.json').exists()}=={16,18,91}
passing=[d for d in receipts if d['exit_status']==0]
modules=[]
for p in sorted(Path('lean').glob('Hist_*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 matches=[d for d in passing if d.get('source_hashes',{}).get(p.name)==sha]
 assert matches,p
 best=matches[-1]
 assert not any('sorryAx' in a for a in best.get('print_axioms',[])),p
 content=p.read_text()
 # Strip comments for the static prohibited-proof construct scan.
 clean=re.sub(r'/\-.*?\-/','',content,flags=re.S)
 clean=re.sub(r'--[^\n]*','',clean)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',clean),p
 modules.append({'module':str(p),'sha256':sha,'passing_attempt':best['attempt'],'axioms':best.get('print_axioms',[])})
pins=json.loads((root/'Hist_source-pins.json').read_text())
for name,info in pins['sources'].items():assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==info['sha256'],name
changed=subprocess.check_output(['git','diff','--name-only','b57e886291','--'],text=True).splitlines()
assert all(p.startswith('lean/Hist_') or p.startswith('evidence/history-20261026/') for p in changed),changed
out={'charged_lean_submissions':100,'actual_lean_invocations':97,'prelaunch_failures':[16,18,91],
 'passing_invocations':len(passing),'failed_invocations':len(receipts)-len(passing),
 'failed_attempts':[d['attempt'] for d in receipts if d['exit_status']!=0],
 'kani_runs':1,'kani_verified_runs':0,'optimized_rust_fixtures':2,
 'lean_wall_seconds':sum(d['wall_seconds'] for d in receipts),
 'lean_max_peak_rss_kib':max(int(d['peak_rss_kib']) for d in receipts),
 'lean_swaps':sorted(set(str(d['swaps']) for d in receipts)),
 'no_current_source_without_passing_exact_snapshot':True,
 'source_pins_match_current_shipped_files':True,'modules':modules,
 'attempts':[{k:d.get(k) for k in ['attempt','command','source_revision','source_tree_dirty','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','source_hashes','limits']} for d in receipts]}
(root/'Hist_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['attempts','modules']},indent=2));print('Current modules',len(modules))
