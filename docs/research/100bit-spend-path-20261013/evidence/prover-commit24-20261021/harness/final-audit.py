#!/usr/bin/env python3
"""Audit this packet without rerunning any formal build."""
import hashlib,json,re,subprocess
from pathlib import Path
BASE='0b214bdbd'
E=Path(__file__).resolve().parent.parent
ROOT=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
D=ROOT/'docs/research/v8-r0-zk-20261009'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
changes=git('diff','--name-only',BASE).splitlines()+git('ls-files','--others','--exclude-standard').splitlines()
shipped=[p for p in changes if p.startswith(('crates/','programs/'))]
protected=[p for p in changes if Path(p).name in ('BuilderSource.lean','BuilderRuntimeJoin.lean','PrivacyR1FinalRelease.lean')]
assert not shipped,shipped
assert not protected,protected
modules=['ProverCommitTrustedStd24','ProverCommitCounter24','ProverCommitMapProgram24',
 'ProverCommitFreshWindow24','ProverCommitFuelFactor24']
new_theorems=[]
for m in modules:
 s=(D/'lean/R1Z'/f'{m}.lean').read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option (maxRecDepth|maxHeartbeats)',s,re.M),m
 ts=re.findall(r'^theorem (\w+)',s,re.M)
 audits=re.findall(r'^#print axioms (\w+)',s,re.M)
 assert sorted(ts)==sorted(audits),(m,ts,audits)
 new_theorems += [f'R1Z.{m}.{t}' for t in ts]
rows=[]
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
 rows += [json.loads(l) for l in p.read_text().splitlines()]
assert sorted(r['attempt'] for r in rows)==list(range(7487,7500))
for r in rows:
 a=r['attempt'];name=Path(r['module']).stem
 snap=E/'lean/sources'/f'attempt-{a}-{name}.lean.txt'
 assert sha(snap)==r['source_sha256'],a
 for k in ('deps_fingerprint','exit_status','wall_time','peak_rss_kib','swaps','source_revision','axioms','errors'):
  assert k in r,(a,k)
 assert r['swaps']==0 and r['memory_limit_mib']==7000 and r['cgroup_memory_max_gib']==8,a
 if r['accepted']:
  for audit in r['axioms']:
   assert 'sorryAx' not in audit
   if 'depends on axioms:' in audit:
    names=re.search(r'\[([^]]*)\]',audit,re.S)[1]
    assert set(x.strip() for x in names.split(',')) <= {'propext','Classical.choice','Quot.sound'}
final=next(r for r in rows if r['attempt']==7499)
assert final['accepted']
assert len(final['axioms'])==24
for n in new_theorems:
 assert any(a.startswith("'"+n+"'") for a in final['axioms']),n
for m,a in zip(modules,[7488,7491,7492,7498,7497]):
 r=next(r for r in rows if r['attempt']==a)
 assert r['accepted'] and r['source_sha256']==sha(D/'lean/R1Z'/f'{m}.lean')
launcher=(E/'harness/run-joint.sh.txt').read_text()
for setting in ['MemoryHigh=$((MX-2))G','MemoryMax=${MX}G','MemorySwapMax=0','TasksMax=64',
 'if [ 0 = 1 ]; then','flock 9']:
 assert setting in launcher,setting
endpoints=['PrivacyR1HeadlineDeployed','ProverCommitDeployedFuel22']
for m in endpoints:
 p=D/'lean/R1Z'/f'{m}.lean'
 assert p.read_text()==git('show',BASE+':'+str(p.relative_to(ROOT)))
s=(D/'lean/R1Z/ProverCommitDeployedFuel22.lean').read_text()
a=s.index('def RustProverRefinement : Prop :=');b=s.index('/--',a)
ref=s[a:b].rstrip()
a=s.index('theorem privacy_headline_deployed');b=s.index(':= by',a)
statement=ref+'\n\n'+s[a:b].rstrip()
report=(D/'r1p-final/PROVER-COMMIT24-20261021.md').read_text()
blocks=re.findall(r'```lean\n(.*?)\n```',report,re.S)
assert blocks==[statement,statement]
assert not any('shippedProverExperiment' in (D/'lean/R1Z'/f'{m}.lean').read_text() for m in modules)
P=ROOT/'docs/research/100bit-spend-path-20261013/lean-candidates/post25-add-small-compatibility-proofs-20261020'
raw=P/'wrapper-provenance/raw-wrapper.lean.txt'
compat=P/'wrapper-provenance/compatibility-wrapper.lean.txt'
external=P/'reference-owner/AspisR1Post25SamplerStd/FunsExternal.lean'
assert 'into_iter_back back' in raw.read_text()
assert 'into_iter_back (back iter)' in compat.read_text()
assert 'core.slice.iter.IterMut T → Array T N' in external.read_text()
out=(E/'lean/out-7499.log').read_text()
assert 'Application type mismatch' in out and 'into_iter_back (back iter) : Std.Array U32' in out
assert '#check_failure into_iter_back back' in (D/'lean/R1Z/ProverCommit24Audit.lean').read_text()
result=dict(base_revision=BASE,audit_revision=git('rev-parse','HEAD').strip(),
 new_theorem_count=len(new_theorems),final_axioms_count=len(final['axioms']),attempts=[r['attempt'] for r in rows],
 accepted_attempts=[r['attempt'] for r in rows if r['accepted']],
 excluded_attempts=[r['attempt'] for r in rows if not r['accepted']],
 shipped_changes=shipped,protected_changes=protected,
 endpoints_unchanged=True,verbatim_before_after_equal=True,premise_removed=False,
 shippedProverExperiment_constructed=False,full_run_joins_proved=False,
 final_lean_receipt=final,
 sampler_provenance=[dict(path=str(p.relative_to(ROOT)),sha256=sha(p)) for p in [raw,compat,external]],
 remaining=['current source gamma/ordinary/query policies and caller nominal carriers',
 'circle caller, all-internal-address classification, retry/error/serialization and native trace joins',
 'concrete source experiment and both independent coupling marginals',
 'trusted-std-only deployed endpoint and successful deletion-only specialization'])
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('final_lean_receipt','sampler_provenance')},indent=2))
