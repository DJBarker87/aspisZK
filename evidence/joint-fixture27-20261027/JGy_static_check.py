from pathlib import Path
import json,re,hashlib,subprocess,collections
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[json.loads(f.read_text()) for f in sorted(P.glob('JGy27_*/receipt.json'))]
assert len(rows)==100 and [int(r['attempt'][-3:]) for r in rows]==list(range(1,101))
valid={(n,h):r for r in rows if r['exit_status']==0 for n,h in r['source_hashes'].items()}
missing=[];violations=[];missing_prints=[]
roots=sorted((R/'lean').glob('JGy_*.lean'))
for f in roots:
 if (f.name,hashlib.sha256(f.read_bytes()).hexdigest()) not in valid:missing.append(f.name)
 text=f.read_text();decls=collections.Counter(re.findall(r'^\s*(?:private )?theorem\s+(\w+)',text,re.M));prints=collections.Counter(re.findall(r'^#print axioms\s+(\w+)',text,re.M))
 for n,c in decls.items():
  if prints[n]<c:missing_prints.append((f.name,n,c,prints[n]))
 for n,l in enumerate(text.splitlines(),1):
  if re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',l):violations.append([str(f),n,l])
assert not missing,missing
assert not violations,violations
assert not missing_prints,missing_prints
assert all(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} for r in rows)
assert all(json.loads((P/(r['attempt']+'-reservation.json')).read_text())['allowed'] is True for r in rows)
base=(P/'JGy_BASE_REVISION.txt').read_text().strip();assert re.fullmatch(r'[0-9a-f]{40}',base)
paths=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
assert all(x.startswith('lean/JGy_') or x.startswith('evidence/joint-fixture27-20261027/') for x in paths)
out=dict(lean_processes=100,kani_runs=0,no_101st_compile=True,retained_checked_proof_modules=len(roots),all_retained_sources_match_passing_receipts=True,no_forbidden_proof_tokens_or_depth_heartbeat_overrides=True,all_new_theorems_have_print_directives=True,all_100_cgroup_limits_exact=True,all_admissions_allowed_true=True,admission_exit_zero_enforced_by='JGy_compile.py requires subprocess returncode==0 AND allowed is True before upload; per-step exit code not separately persisted',sequencer_guard='One pre-admission no-Lean refusal reserved070; not an additional compile',only_owned_paths=True,shipped_changes=False,swaps=sum(int(r['swaps'] or 0) for r in rows),failed_attempts=[r['attempt'] for r in rows if r['exit_status']])
(P/'JGy_STATIC_FINAL.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
