#!/usr/bin/env python3
"""Verify this packet's receipts and precise unchanged endpoint; no build rerun."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent.parent
ROOT=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
D=ROOT/'docs/research/v8-r0-zk-20261009';L=D/'lean/R1Z'
BASE='87684ed0d'
def git(*a):return subprocess.check_output(['git',*a],text=True,cwd=ROOT)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
changes=set(git('diff','--name-only',BASE).splitlines()+git('ls-files','--others','--exclude-standard').splitlines())
assert not any(p.startswith(('crates/','programs/')) for p in changes)
assert not any(Path(p).stem in ['SourceIdentification','RustRuntimeJoin','PrivacyR1FinalRelease'] for p in changes)
assert not any(Path(p).suffix in ['.olean','.llbc','.elf','.gz'] for p in changes)
mods=['ProverCommitProduct25','ProverCommitProductRun25','ProverCommitCircle25',
 'ProverCommitArrayIndex25','ProverCommitPolicies25','ProverCommitPack25',
 'ProverCommitPackWindows25','ProverCommitStreamPack25','ProverCommitProductOracle25',
 'ProverCommitProductCarrier25']
audit_names=[]
for m in mods:
 s=(L/(m+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option (maxRecDepth|maxHeartbeats)',s,re.M),m
 ts=re.findall(r'^theorem (\w+)',s,re.M);audits=re.findall(r'^#print axioms (\w+)',s,re.M)
 assert set(ts)<=set(audits),(m,ts,audits)
 audit_names += ['R1Z.'+m+'.'+t for t in audits]
rows=[]
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
 rows.extend(json.loads(l) for l in p.read_text().splitlines())
assert len(set(r['attempt'] for r in rows))==len(rows)
for r in rows:
 a=r['attempt'];assert 7500<=a<=7699
 snap=E/'lean/sources'/f'attempt-{a}-{Path(r["module"]).stem}.lean.txt'
 assert sha(snap)==r['source_sha256'],a
 for key in ['deps_fingerprint','exit_status','wall_time','peak_rss_kib','swaps','source_revision','axioms','errors']:
  assert key in r,(a,key)
 assert r['swaps']==0 and r['memory_limit_mib']==7000 and r['cgroup_memory_max_gib']==8,a
 if r['accepted']:
  assert not r['errors'],(a,r['errors'])
  for line in r['axioms']:
   assert 'sorryAx' not in line,(a,line)
   if 'depends on axioms:' in line:
    assert set(x.strip() for x in re.search(r'\[([^]]*)\]',line,re.S)[1].split(',')) <= {'propext','Classical.choice','Quot.sound'}
final=max((r for r in rows if r['module']=='R1Z/ProverCommit25Audit.lean' and r['accepted']),key=lambda r:r['attempt'])
assert len(final['axioms'])==len(audit_names)+2,(len(final['axioms']),len(audit_names))
for n in audit_names:assert any(x.startswith("'"+n+"'") for x in final['axioms']),n
for m in mods:
 assert any(r['accepted'] and r['module']=='R1Z/'+m+'.lean' and r['source_sha256']==sha(L/(m+'.lean')) for r in rows),m
for r in json.loads((E/'sampler-owners.json').read_text()):
 p=D/'lean'/(r['module'].replace('.','/')+'.lean')
 assert r['promoted_sha256']==sha(p),r['module']
 assert any(a['accepted'] and a['module']==r['module'].replace('.','/')+'.lean' and a['source_sha256']==sha(p) for a in rows),r['module']
for f in ['PrivacyR1HeadlineDeployed','ProverCommitDeployedFuel22']:
 p=L/(f+'.lean');assert p.read_text()==git('show',BASE+':'+str(p.relative_to(ROOT)))
s=(L/'ProverCommitDeployedFuel22.lean').read_text();a=s.index('def RustProverRefinement : Prop :=');b=s.index('/--',a);statement=s[a:b].rstrip();a=s.index('theorem privacy_headline_deployed');b=s.index(':= by',a);statement+='\n\n'+s[a:b].rstrip()
report=(D/'r1p-final/PROVER-COMMIT25-20261021.md').read_text()
assert re.findall(r'```lean\n(.*?)\n```',report,re.S)==[statement,statement]
assert (E/'endpoint-deletion.diff').read_bytes()==b''
for name in ['addsmall-v1','addsmall-v2','addsmall-v3','lowdigits-v1','divisionpass-v1','traversal-v1']:
 d=E/'receipts'/name;pin=json.loads((d/'source.json').read_text());assert sha(d/'source.rs.txt')==pin['source_sha256']
 r=json.loads((d/'receipt.json').read_text());assert r['swaps']==0
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 if name in ['addsmall-v3','traversal-v1']:assert r['exit_status']==0
 if name in ['lowdigits-v1','divisionpass-v1']:assert r['exit_status']==124
launcher=(E/'harness/run-joint.sh.txt').read_text()
for t in ['MemoryHigh=$((MX-2))G','MemoryMax=${MX}G','MemorySwapMax=0','TasksMax=64','if [ 0 = 1 ]; then','flock 9']:assert t in launcher
result=dict(base_revision=BASE,audit_revision=git('rev-parse','HEAD').strip(),final_attempt=final['attempt'],
 final_audit_count=len(final['axioms']),accepted_attempts=[r['attempt'] for r in rows if r['accepted']],
 excluded_attempts=[r['attempt'] for r in rows if not r['accepted']],
 shipped_changes=[],protected_changes=[],endpoints_unchanged=True,premises_removed=0,
 source_experiment_constructed=False,whole_run_joins_proved=False,
 proved=['independent rejection product RunJoin component','persistent-window packing and full finite-oracle marginal','adaptive observer history outside existing seedGuess','circle policy and block nominal transport','unconditional owned gamma/ordinary/rho policies and ranks','Kani shipped/indexed add-small equality'],
 open=['complete low-digit source/control arithmetic composition','unconditional concrete query policy/source join','full caller/validator/retry/serialization/native trace composition','shippedProverExperiment and real/ideal WholeRunJoins','TrustedStd/P6/P7-only privacy endpoint'],
 final_receipt=final)
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['final_receipt','accepted_attempts','excluded_attempts']},indent=2))
