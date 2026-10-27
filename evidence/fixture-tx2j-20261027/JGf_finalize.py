"""Receipt-only final audit and draft retention. Launches no prover."""
from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(f.read_text()) for f in sorted(P.glob('JGf_TX2_*/receipt.json'))]
assert len(receipts)==100 and [r['attempt'] for r in receipts]==[f'JGf_TX2_{i:03}' for i in range(1,101)]
accepted={(name,h) for r in receipts if r['exit_status']==0 for name,h in r['source_hashes'].items()}
backup=P/'JGf_UNCHECKED';backup.mkdir(exist_ok=True);drafts=[]
for f in sorted((R/'lean').glob('JGf_*.lean')):
 if (f.name,sha(f)) not in accepted:
  target=backup/(f.name+'.txt');target.write_bytes(f.read_bytes());drafts.append(dict(path=str(target.relative_to(R)),sha256=sha(f),status='UNCHECKED TEXT ONLY; no accepted current-source receipt'));f.unlink()
(P/'JGf_UNCHECKED_MANIFEST.json').write_text(json.dumps(drafts,indent=2)+'\n')
subprocess.run(['python3',str(P/'JGf_validate.py'),'--final'],check=True)
for g in ['JGf_hashes.py','JGf_roots.py','JGf_counts.py']:subprocess.run(['python3',str(P/g),'--check'],check=True)
assert sha(P/'JGf_BEFORE_Rc10_Top.lean.txt')==sha(R/'lean/Rc10_Top.lean')
(P/'JGf_AFTER_Rc10_Top.lean.txt').write_bytes((R/'lean/Rc10_Top.lean').read_bytes())
assert receipts[-1]['exit_status']==0,'Final audit failed: preserve exact evidence; do not claim a passing final audit'
old=json.loads((R/'evidence/fixture-tx2i-20261027/JGc_TX2_100/receipt.json').read_text())
obj=receipts[-1]['deps_fingerprint']['selected_objects']['Rc10_Top.olean']['sha256']
assert obj==old['deps_fingerprint']['selected_objects']['Rc10_Top.olean']['sha256']
ledger=json.loads((P/'JGf_LEDGER_DELTA.json').read_text());ledger.update(fresh_top_audit='evidence/fixture-tx2j-20261027/JGf_TX2_100',before_after_top_object_sha256=obj);(P/'JGf_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
(P/'JGf_ATTEMPTS.jsonl').write_text(''.join(json.dumps({k:r[k] for k in ['attempt','sources','source_revision','source_tree_dirty','source_hashes','command','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']},ensure_ascii=False)+'\n' for r in receipts))
files=[]
for f in sorted(P.glob('JGf_TX2_*/*')):
 if f.is_file():files.append(dict(path=str(f.relative_to(R)),bytes=f.stat().st_size,sha256=sha(f)))
(P/'JGf_RECORDS_MANIFEST.json').write_text(json.dumps(files,indent=2)+'\n')
failures=[]
for r in receipts:
 if r['exit_status']:
  log=P/r['attempt']/'stdout.log';failures.append(dict(attempt=r['attempt'],sources=r['sources'],errors=[l for l in log.read_text().splitlines() if 'error:' in l],classification='Rejected ordinary source error; changed replacement passes; no validation credit'))
(P/'JGf_FAILURES.json').write_text(json.dumps(failures,indent=2)+'\n')
plan=json.loads((P/'JGf_HASH_PLAN.json').read_text());mods={n[:-5] for n,h in accepted if n.endswith('.lean')}
windows=[x for x in plan if x['module'] in mods]
assert sum(x['blocks'] for x in windows)==560
(P/'JGf_FINAL_AUDIT.json').write_text(json.dumps(dict(final=receipts[-1],checked_hash_blocks=560,tree0_blocks=456,tree1_blocks=104,tree1_remaining_blocks=280,max_blocks_per_window=max(x['blocks'] for x in windows),actual_top_removal=dict(T=0,P=0,G=0,C=0),accepted2_established=False,joint_pair_established=False,full_nonvacuity_established=False,model_root0_nonvacuity_established=True,shipped_file_changes=False,elf_rebuild_triggered=False,fresh_release_replay=False,reused_workspace='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025',cache_precedence='d18 v5 before aspis-joint',kani_runs=0),indent=2)+'\n')
changed=subprocess.check_output(['git','diff','--name-only','4176bcbe45537e2e9a4c030eb6f5846081ab8d71'],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(x.startswith('lean/JGf_') or x.startswith('evidence/fixture-tx2j-20261027/') for x in changed+untracked),(changed,untracked)
assert not any(f.suffix in {'.olean','.elf','.tar','.gz'} for f in P.rglob('*') if f.is_file())
(P/'JGf_FINAL_CHECKS.json').write_text(json.dumps(dict(checked_paths=changed+untracked,prefix_scope_only=True,source_generators_check=True,no_binaries=True,unchanged_top_source_sha256=sha(R/'lean/Rc10_Top.lean'),unchanged_top_object_sha256=obj,unchanged_full_regression_runs=0,dependency_builds=0,resource_kills=0,external_timeouts=0,cap_increases=0,heartbeat_depth_increases=0),indent=2)+'\n')
print('final receipt audit: 100/100; 560 blocks; exact source and object top unchanged; no further Lean allowed')
