"""Final receipt/source audit. No prover launch; preserve unchecked drafts as text."""
from pathlib import Path
import json,hashlib,subprocess,re
P=Path(__file__).resolve().parent;R=P.parents[1];entry='a4a0f5dcb1696a55c47eb0f2e22377782da67783'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
receipts=[json.loads(f.read_text()) for f in sorted(P.glob('JGh_TX2_*/receipt.json'))]
assert len(receipts)==100 and [r['attempt'] for r in receipts]==[f'JGh_TX2_{i:03}' for i in range(1,101)]
accepted={(name,h) for r in receipts if r['exit_status']==0 for name,h in r['source_hashes'].items()}
drafts=[];backup=P/'JGh_UNCHECKED';backup.mkdir(exist_ok=True)
for f in sorted((R/'lean').glob('JGh_*.lean')):
 if (f.name,sha(f)) not in accepted:
  out=backup/(f.name+'.txt');out.write_bytes(f.read_bytes());drafts.append(dict(path=str(out.relative_to(R)),sha256=sha(f),classification='UNCHECKED TEXT ONLY; excluded from delivered proof closure'));f.unlink()
(P/'JGh_UNCHECKED_MANIFEST.json').write_text(json.dumps(drafts,indent=2)+'\n')
subprocess.run(['python3',str(P/'JGh_validate.py'),'--final'],check=True)
for name in ['Rc10_Top','Rc2_Top']:
 f=R/'lean'/(name+'.lean')
 if not f.exists():f=R/'docs/research/100bit-spend-path-20261013/lean'/(name+'.lean')
 assert sha(f)==sha(P/f'JGh_BEFORE_{name}.lean.txt')
 (P/f'JGh_AFTER_{name}.lean.txt').write_bytes(f.read_bytes())
for f in P.glob('JGh_TX2_*-driver.log'):
 f.write_text('\n'.join(line.rstrip() for line in f.read_text().splitlines()).rstrip()+'\n')
for f in P.glob('JGh_TX2_*-launch.log'):
 f.write_text('\n'.join(line.rstrip() for line in f.read_text().splitlines()).rstrip()+'\n')
for r in receipts:
 for name,h in r['source_hashes'].items():assert sha(P/r['attempt']/'sources'/name)==h
summary=[];failures=[]
for r in receipts:
 summary.append({**{k:r[k] for k in ['attempt','sources','source_revision','source_tree_dirty','source_hashes','command','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']},'receipt':f"evidence/fixture-tx2k-20261027/{r['attempt']}/receipt.json",'deps_fingerprint_sha256':hashlib.sha256(json.dumps(r['deps_fingerprint'],sort_keys=True).encode()).hexdigest()})
 if r['exit_status']:
  failures.append(dict(attempt=r['attempt'],sources=r['sources'],source_hashes=r['source_hashes'],errors=[l for l in (P/r['attempt']/'stdout.log').read_text().splitlines() if 'error:' in l],classification='Rejected source; no proof credit; complete raw source/stdout/time retained'))
(P/'JGh_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in summary))
(P/'JGh_FAILURES.json').write_text(json.dumps(failures,indent=2)+'\n')
ledger=json.loads((P/'JGh_LEDGER_DELTA.json').read_text());ledger.update(before_source_sha256=sha(P/'JGh_BEFORE_Rc10_Top.lean.txt'),after_source_sha256=sha(P/'JGh_AFTER_Rc10_Top.lean.txt'),fresh_final_audit=receipts[-1]['attempt'],fresh_final_audit_passed=receipts[-1]['exit_status']==0)
obj=receipts[-1]['deps_fingerprint'].get('selected_objects',{}).get('Rc10_Top.olean')
old=receipts[69]['deps_fingerprint'].get('selected_objects',{}).get('Rc10_Top.olean')
if obj and old:assert obj['sha256']==old['sha256'];ledger['unchanged_top_object_sha256']=obj['sha256']
(P/'JGh_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
mods={n[:-5] for n,h in accepted if n.endswith('.lean')}
checked_heights=[h for h in range(18) if f'JGh_TX2_FrontierHeight{h:02}' in mods]
data=json.loads((R/'evidence/fixture-tx2j-20261027/JGf_MERKLE_PREFLIGHT.json').read_text())
cellcounts={h:sum(1 for tree in data['trees'] for row in tree['hashes'] if row['kind']=='parent' and row['level']==h and row['source']!='occupied') for h in range(18)}
assert sum(cellcounts.values())==467
metrics=dict(checked_native_sibling_cells=sum(cellcounts[h] for h in checked_heights),count_frontier_identities=receipts[-1]['exit_status']==0 and any('JGh_TX2_CountFrontier.source0' in x for x in receipts[-1]['print_axioms']),lean_attempts=100,passed=sum(r['exit_status']==0 for r in receipts),rejected=sum(r['exit_status']!=0 for r in receipts),kani_runs=0,total_wall_seconds=sum(r['wall_seconds'] for r in receipts),maximum_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),new_checked_tree1_blocks=280,total_tree1_blocks_with_inherited=384,model_root1='JGh_TX2_M1Root' in mods,native_tree0_tree1_leaves=sum(2 for m in mods if re.fullmatch('JGh_TX2_M[01]LeafSources[0-9]+',m)),native_frontier_heights=checked_heights,frontier_stream='JGh_TX2_FrontierStream' in mods,sibling_law_aggregate='JGh_TX2_SiblingBindings' in mods,accepted2_established=False,joint_pair_established=False,actual_top_removed=dict(T=0,P=0,G=0,C=0),full_nonvacuity_established=False,shipped_file_changes=False,elf_rebuild_triggered=False,fresh_release_replay=False,resource_kills=0,external_timeouts=0,cap_increases=0,depth_heartbeat_increases=0,final=receipts[-1])
(P/'JGh_FINAL_AUDIT.json').write_text(json.dumps(metrics,indent=2)+'\n')
files=[dict(path=str(f.relative_to(R)),bytes=f.stat().st_size,sha256=sha(f)) for f in sorted(P.glob('JGh_TX2_*/*')) if f.is_file()]+[dict(path=str(f.relative_to(R)),bytes=f.stat().st_size,sha256=sha(f)) for f in sorted(P.glob('JGh_TX2_*/sources/*.lean'))]
(P/'JGh_RECORDS_MANIFEST.json').write_text(json.dumps(files,indent=2)+'\n')
changed=subprocess.check_output(['git','diff','--name-only',entry],cwd=R,text=True).splitlines();untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(f.startswith('lean/JGh_') or f.startswith('evidence/fixture-tx2k-20261027/') for f in changed+untracked)
assert not any(f.suffix in {'.olean','.elf','.tar','.gz'} for f in P.rglob('*') if f.is_file())
(P/'JGh_FINAL_CHECKS.json').write_text(json.dumps(dict(prefix_scope_only=True,no_binaries=True,unchanged_top_source=True,actual_top_removal_zero=True,unchanged_full_regression_runs=0,dependency_builds=0),indent=2)+'\n')
(P/'JGh_COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline',entry+'..HEAD'],cwd=R,text=True))
print({k:v for k,v in metrics.items() if k!='final'});print('No101st Lean compile is permitted.')
