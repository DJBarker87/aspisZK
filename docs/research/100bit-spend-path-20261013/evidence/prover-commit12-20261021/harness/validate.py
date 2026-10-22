#!/usr/bin/env python3
import hashlib,json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Every recorded Rust input must resolve to the baseline or a literal trial.
variants={}
for p in (E/'rust-sources').glob('*'):
 name=re.sub(r'-v[0-9]+(?=\.rs$)','',p.name.removesuffix('.txt'))
 variants.setdefault(name,set()).add(sha(p))
variants.setdefault('transcript.rs',set()).add(sha(E/'rust-sources/transcript-v1.rs.txt'))
variants.setdefault('r1_wire.rs',set()).add(sha(E/'rust-sources/r1_wire-v1.rs.txt'))
for p in E.glob('*-inputs.json'):
 x=json.loads(p.read_text())
 if not isinstance(x,dict):continue
 x=x.get('source_hashes',x)
 for f,h in x.items():
  if not isinstance(h,str) or len(h)!=64:continue
  baseline=Path(f)
  candidates={sha(baseline)} if baseline.is_file() else set()
  candidates.update(variants.get(Path(f).name,set()))
  assert h in candidates,(p,f,h)
passed=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 x=json.loads(p.read_text()); lim=x['limits']
 assert lim=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},(p,lim)
 assert x['swaps']==0
 assert x['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4'
 assert x['command'][x['command'].index('-j')+1]=='4'
 assert '--unwinding-assertions' in x['command']
 if x['exit_status']==0:
  assert 'VERIFICATION:- SUCCESSFUL' in p.with_name('stdout.log').read_text(),p
  passed.append(p.parent.name)
assert all((p/'receipt.json').exists() for p in (E/'receipts').iterdir() if p.is_dir())
assert {'transcript-queries-prefix-v1','mask-iteration-v4','source-iteration-v1','transcript-absorb-v1','transcript-block-v1','transcript-new-v1','semantic-block-v1','semantic-new-v2','semantic-row25-capacity-v1','binary-parent-v1'}<=set(passed)
# No unsupported extraction axiom is admitted by a successful compiler exit.
allowed={'propext','Classical.choice','Quot.sound'}
for p in (E/'lean').glob('attempts-*.jsonl'):
 for line in p.read_text().splitlines():
  x=json.loads(line)
  assert x['swaps']==0
  if x['exit_status']==0 and x['module']!='R1Z/ProverCommitShippedAxiomAudit.lean':
   assert x['axioms']
   for a in x['axioms']:
    match=re.search(r'\[([^]]*)\]',a,re.S)
    assert not match or {t.strip() for t in match[1].split(',')}<=allowed,(x['attempt'],a)
for mod,a in [('ProverCommitShippedSchedule',8359),('ProverCommitShippedTransport',8362),('ProverCommitBuilderDeletionObstruction',8360)]:
 x=json.loads((E/f'lean/lean-{a}.json').read_text());assert sha(L/'R1Z'/f'{mod}.lean')==x['source_sha256']
meta=json.loads((E/'scalar-harness-metadata.json').read_text())
for family in ['mask','source']:
 matches=[x['harness'] for x in meta if x['harness']['pretty_name'].endswith(f'::{family}_iteration')]
 assert matches
 for h in matches:
  st=h['attributes']['verified_stubs']
  assert 'prover_commit_reference::next' in st and len(st)==2,st
c=json.loads((E/'callback-coverage.json').read_text());assert not c['all_family_coverage_closed']
for r in c['rows']:assert sha(Path(r['source']))==r['source_sha256']
if (E/'headline-before.lean.txt').exists():
 assert (E/'headline-before.lean.txt').read_bytes()==(E/'headline-after.lean.txt').read_bytes()
 assert (E/'headline-deletions.diff').read_bytes()==b''

m=json.loads((E/'manifest.json').read_text())
for f,h in m['adopted_lean'].items():assert sha(Path(f))==h
x=json.loads((E/'lean/attempts-8363-8364.jsonl').read_text())
assert x['exit_status']==0
assert [a.split("'")[1] for a in x['axioms']]==m['expected_axioms']
q=json.loads((E/'query-prefix.json').read_text())
original=Path('crates/aspis-r1-cost-probe/src/transcript.rs')
assert sha(original)==q['source_sha256']
assert q['prefix'] in original.read_text()
assert q['prefix'].replace('self.','actual.') in (E/'rust-sources/transcript.rs').read_text()

print(json.dumps(dict(result='passed',passed_rust=passed,axioms=sorted(allowed),coverage_closed=False),indent=2))
