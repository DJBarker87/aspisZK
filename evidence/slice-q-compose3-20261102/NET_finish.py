from pathlib import Path
import json,hashlib,re,subprocess,collections
E=Path(__file__).resolve().parent;R=E.parent.parent
assert not (E/'NET_ACTIVE.json').exists()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
obj=lambda p:json.loads(Path(p).read_text())
CAPS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
records=[obj(p) for p in sorted(E.glob('NET_*/receipt.json'))]
count=collections.Counter(r['kind'] for r in records)
assert count==dict(kani=100,lean=34,extract=1),count
assert all(r['limits']==CAPS and int(r['swaps'])==0 for r in records)
log=[json.loads(l) for l in (E/'NET_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(log)==len(records)==len({r['attempt'] for r in log})
assert {r['attempt'] for r in log}=={r['attempt'] for r in records}
audit=obj(E/'NET_L034/receipt.json');assert audit['exit_status']==0
new=[];proofs=[]
for path in sorted(E.glob('NET_*.lean')):
 if path.stem=='NET_Audit':continue
 source=path.read_text();names=[path.stem+'.'+n for n in re.findall(r'^theorem\s+([A-Za-z_][A-Za-z_0-9]*)',source,re.M)]
 if not names:continue
 assert not re.search(r'^\s*(axiom|opaque)\b|\bsorry\b|\badmit\b|\bnative_decide\b|set_option\s+(maxHeartbeats|maxRecDepth)',source,re.M)
 valid=[r for r in records if r['kind']=='lean' and r.get('module')==path.stem and r['exit_status']==0 and r['source_hashes'].get(path.name)==sha(path)]
 assert valid,path
 r=valid[-1];new+=names
 for name in names:
  line=next(x for x in audit['print_axioms'] if x.startswith("'"+name+"'"))
  if 'does not depend on any axioms' not in line:
   ax=re.search(r'axioms: \[([^]]*)\]',line);assert ax
   assert set(x.strip() for x in ax[1].split(','))<={'propext','Classical.choice','Quot.sound'}
 proofs.append(dict(module=path.stem,source=str(path.relative_to(R)),source_sha256=sha(path),receipt=r['attempt'],theorems=names))
assert len(new)==41
metrics=[]
for r in records:
 a=r['attempt'];metrics.append(dict(attempt=a,kind=r['kind'],target=r.get('module',r.get('target',r.get('command'))),exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_tree_dirty=r.get('source_tree_dirty'),source_hashes_sha256=hashlib.sha256(json.dumps(r['source_hashes'],sort_keys=True).encode()).hexdigest(),print_axioms=r['print_axioms'],limits=r['limits'],receipt=str((E/a/'receipt.json').relative_to(R)),receipt_sha256=sha(E/a/'receipt.json')))
(E/'NET_METRICS.json').write_text(json.dumps(metrics,indent=1)+'\n')
(E/'NET_PROOF_AUDIT.json').write_text(json.dumps(dict(new_theorem_count=len(new),new_theorems=new,accepted_modules=proofs,coimport_audit='NET_L034',axioms=['propext','Classical.choice','Quot.sound'],failed_lean_excluded=[r['attempt'] for r in records if r['kind']=='lean' and r['exit_status']!=0]),indent=1)+'\n')
delta=obj(E/'NET_LEDGER_DELTA.json');assert delta['q_functions_closed']==61 and delta['edge_closed']==164
manifest={str(p.relative_to(E)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(E.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.name not in ['NET_FINAL_INPUTS.json','NET_FINAL_REVIEW.json','NET_ACTIVE.json']}
(E/'NET_FINAL_INPUTS.json').write_text(json.dumps(manifest,indent=1)+'\n')
review=dict(inputs_manifest_sha256=sha(E/'NET_FINAL_INPUTS.json'),frozen_rust_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',proof_worktree_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),proof_source_snapshot='NET_PROOF_AUDIT.json plus per-target archived source hashes; validation precedes final commit',branch=subprocess.check_output(['git','branch','--show-current'],cwd=R,text=True).strip(),budget=dict(used=dict(count),limits=dict(kani=100,lean=80,extract=10)),delta=delta,metrics_sha256=sha(E/'NET_METRICS.json'),proof_audit_sha256=sha(E/'NET_PROOF_AUDIT.json'),validator_sha256=sha(E/'NET_validate.py'),tests_sha256=sha(E/'NET_tests.py'),validator_tests=27,peer_denial_tests=12,prefix_source_tests=8,geometry_source_tests=6,geometry_window_tests=6,final_audit=dict(attempt='NET_L034',exit_status=0,wall_seconds=audit['wall_seconds'],peak_rss_kib=audit['peak_rss_kib'],swaps=audit['swaps'],new_theorems=41,axioms='standard only'),excluded_native_timeouts=['NET_K089','NET_K090','NET_K091'],unresolved_prelaunch='NET_K007: no scope or receipt; no credit; never resubmitted',unused_attempt_identifier='NET_K008',copy_patch_sha256=sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'),suspended_or_quarantined_new_harnesses=[],shipped_files_changed=False,elf_rebuild_trigger=False,elf_pins_status='Inherited unchanged pins, no new rebuild or source-to-ELF claim',retained_trust=['NativeContractSemanticTransport (P6/D188 option A reclassification)','RootPhysicalInterpretation','Allocator (existing runtime item)','Existing source/ABI/std/runtime and source-to-ELF assumptions'],cache_exports_sha256=sha(E/'NET_CACHE_EXPORTS.json'),cache_export='Own cache NET_exports_20261104; hashes unchanged after move; NET_run.py resolves it before earlier caches',security_target_established=False,remaining_lean_extraction_budget='46 Lean/9 extraction unused: every remaining member requires missing native evidence or an outside-Q/installed-cohort boundary; independent gather/trace/KMX Lean work completed. See NET_REMAINING.md member by member.')
(E/'NET_FINAL_REVIEW.json').write_text(json.dumps(review,indent=1)+'\n')
print(json.dumps(dict(budget=dict(count),new_theorems=len(new),functions=61,edges=164,roots=delta['roots'])))
