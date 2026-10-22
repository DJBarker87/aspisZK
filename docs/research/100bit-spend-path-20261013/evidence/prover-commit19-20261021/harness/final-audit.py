"""Audit this pass's exact source/evidence closure; does not run a release build."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
 rows += [json.loads(x) for x in p.read_text().splitlines()]
by_attempt={x['attempt']:x for x in rows}
assert len(rows)==len(by_attempt)
standard={'propext','Classical.choice','Quot.sound'}
accepted=[]
for x in rows:
 a=x['attempt'];name=Path(x['module']).stem
 snap=E/'lean/sources'/f'attempt-{a}-{name}.lean.txt'
 assert sha(snap)==x['source_sha256'],(a,snap)
 out=(E/'lean'/f'out-{a}.log').read_text()
 assert x['exit_status']==int(re.search(r'^exit=(\d+)',out,re.M)[1])
 if x['accepted']:
  assert x['exit_status']==0 and x['swaps']==0
  assert x['cgroup_memory_max_gib']==8 and x['memory_limit_mib']==7000
  assert x['peak_rss_kib']>0 and x['wall_time'] and x['source_revision']
  assert 'sorryAx' not in out
  for _,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",out,re.S):
   assert set(re.findall(r'[\w.]+',axioms)) <= standard
  accepted.append(a)
changed_lean=subprocess.check_output(['git','diff','--name-only','28776b162','--',str(L)],text=True).splitlines()
# Include new untracked or staged modules during pre-commit audit.
changed_lean+=subprocess.check_output(['git','ls-files','--others','--exclude-standard',str(L)],text=True).splitlines()
changed_lean=sorted(set(changed_lean))
for name in changed_lean:
 p=Path(name)
 if p.suffix!='.lean':continue
 text=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',text),name
 module=str(p.relative_to(L))
 assert any(x['module']==module and x['accepted'] and x['source_sha256']==sha(p) for x in rows),name
 if '/AspisR1Simulator' not in name:
  assert not re.search(r'set_option (maxHeartbeats|maxRecDepth)',text),name
au=by_attempt[8704];audit=(E/'lean/out-8704.log').read_text()
required=re.findall(r'^#print axioms (\S+)',(L/'R1Z/ProverCommit19Audit.lean').read_text(),re.M)
seen=re.findall(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)",audit,re.M)
assert au['accepted'] and len(required)==42 and set(required)==set(seen)
for p in (E/'extraction').glob('*/promotion.json'):
 for item in json.loads(p.read_text()):
  raw=Path(item['raw']);promoted=Path(item['promoted'])
  assert sha(raw)==item['raw_sha256'] and sha(promoted)==item['promoted_sha256']
  assert promoted.read_text()==raw.read_text().replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')
for job in ['sim-concat-owned-v3','sim-insert-owned-v2']:
 x=json.loads((E/'extraction'/(job+'-llbc.json')).read_text())
 assert x['has_errors'] is False and x['size_bytes']>0 and x['sha256']
rust=json.loads((E/'rust-attempts.json').read_text())
for x in rust:
 if not x['accepted']:continue
 assert x['exit_status']==0 and x['swaps']==0
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['peak_rss_kib']>0 and x['wall_seconds']>0 and x['source_revision']
 if '-charon' not in x['name'] and '-aeneas' not in x['name']:
  assert 'VERIFICATION:- SUCCESSFUL' in (E/'receipts'/x['name']/'stdout.log').read_text()
for x in json.loads((E/'source-binding.json').read_text()):
 assert sha(Path(x['path']))==x['local_sha256'] and x['production_prefix_identical']
base='28776b162'
assert subprocess.check_output(['git','show',base+':crates/aspis-prover/src/state_only_entropy.rs'])==Path('crates/aspis-prover/src/state_only_entropy.rs').read_bytes()
assert Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean').read_bytes()==(E/'endpoint-after.lean.txt').read_bytes()
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert not any(Path(p).name in ['SourceIdentification.lean','RustRuntimeJoin.lean','PrivacyR1FinalRelease.lean'] for p in changed)
for p in E.rglob('*'):
 if not p.is_file():continue
 assert p.suffix not in ['.olean','.llbc','.tar','.gz','.elf'],p
 assert p.read_bytes()[:4] != b'\x7fELF',p
result=dict(status='passed',source_base_revision=base,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 accepted_lean_attempts=accepted,excluded_lean_attempts=[x['attempt'] for x in rows if not x['accepted']],
 final_audit_attempt=8704,final_axioms_audits=len(seen),accepted_axiom_allowlist=sorted(standard),new_axioms_introduced=False,
 accepted_rust_targets=[x['name'] for x in rust if x['accepted']],
 source_production_prefixes_identical=True,concurrent_owner_sources_untouched=True,
 deployed_privacy='conditional on seed-augmented RustProverRefinement; explicit error remains below 2^-100',
 shippedProverExperiment_constructed=False,full_simulator_extraction_complete=False,
 frozen_release_manifest_replayed=False,scope='one final cached audit of changed proof cone; target not yet established')
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
