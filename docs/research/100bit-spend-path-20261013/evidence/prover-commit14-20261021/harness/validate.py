#!/usr/bin/env python3
"""Evidence/source preflight. No compiler or regression is run here."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.argv[1:] == ['--check']
E=Path(__file__).resolve().parent.parent
R=Path.cwd();L=R/'docs/research/v8-r0-zk-20261009/lean'
m=json.loads((E/'manifest.json').read_text())
for name,sha in m['sources'].items():
 p=R/name;assert hashlib.sha256(p.read_bytes()).hexdigest()==sha,name
 if p.suffix=='.lean':
  text=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',text),name
  if 'AspisR1ProverMaterial14' not in name:assert not re.search(r'set_option (maxRecDepth|maxHeartbeats)',text),name
assert (L/'AspisR1ProverMaterial14/Funs.lean').read_bytes()==(E/'extraction/generated-v2-Funs.lean.txt').read_bytes()
assert (E/'headline-before.lean.txt').read_bytes()==(E/'headline-after.lean.txt').read_bytes()==(L/'R1Z/ProverCommitAdmittedEndpoint.lean').read_bytes()
assert not (E/'headline-deletions.diff').read_bytes()
assert (E/'rust-sources/prover_commit_reference.rs').read_text().startswith((R/'crates/aspis-prover/src/prover_commit_reference.rs').read_text())
# Original shipped functions remain byte-identical before the proof-only harnesses.
assert (E/'rust-sources/state_only_hiding.rs').read_text().split('\n#[cfg(kani)]\n')[0] == (R/'crates/aspis-prover/src/state_only_hiding.rs').read_text().split('\n#[cfg(kani)]\n')[0]
for f in (E/'lean').glob('attempts-*.jsonl'):
 for line in f.read_text().splitlines():
  x=json.loads(line)
  if x['accepted']:
   assert not x['errors'],x['attempt']
   for ax in x['axioms']:
    found=re.search(r'\[([^]]*)\]',ax)
    if found:assert set(re.findall(r'[\w.]+',found[1])) <= {'propext','Classical.choice','Quot.sound'},(x['attempt'],ax)
if (E/'rust-attempts.json').exists():
 for x in json.loads((E/'rust-attempts.json').read_text()):
  assert x['accepted'] == (x['exit_status']==0),x['name']
  assert x['swaps']==0 and x['limits']['memory.swap.max']=='0',x['name']
  assert x['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4',x['name']
  if x['accepted']:
   output=(E/'receipts'/x['name']/'stdout.log').read_text()
   target=x['command'][x['command'].index('--harness')+1]
   assert 'Checking harness '+target in output and 'VERIFICATION:- SUCCESSFUL' in output,x['name']
   assert '1 successfully verified harnesses, 0 failures, 1 total' in output,x['name']
  assert sum(r['bytes'] for r in json.loads((E/(x['name']+'-inputs.json')).read_text())['reservations'])+8*2**30<=55*2**30,x['name']
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in ['.olean','.llbc','.tar','.gz','.elf','.bin'],str(p)
assert not m['all_family_coverage_closed'] and not m['real_execution_join_closed'] and not m['ideal_execution_join_closed']
print('Source manifest, accepted Lean audits, extraction identity, unchanged headline, and proof-only source scope: PASS')
