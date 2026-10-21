#!/usr/bin/env python3
"""Validate the frozen source/evidence bundle; --check is preflight-only."""
import hashlib,json,re,sys
from pathlib import Path
E=Path(__file__).resolve().parent.parent
M=json.loads((E/'manifest.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for p,expected in M['sources'].items():
 p=Path(p);assert p.stat().st_size==expected['size_bytes'] and sha(p)==expected['sha256'],p
 if p.suffix=='.lean':
  s=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b',s),p
  assert not re.search(r'^\s*(axiom|set_option maxRecDepth|set_option maxHeartbeats)\b',s,re.M),p
assert (E/'headline-specialized-before.lean.txt').read_bytes()==(E/'headline-specialized-after.lean.txt').read_bytes()
assert not (E/'headline-deletions.diff').read_bytes()
raw=(E/'extraction/generated-Funs.lean.txt').read_text()
old=Path('docs/research/v8-r0-zk-20261009/lean/AspisR1ProverStep8/Funs.lean').read_text()
def definitions(s):
 out={}
 for m in re.finditer(r'^def (\S+)',s,re.M):
  end=s.find('\n/--',m.start())
  if end<0:end=s.find('\nend ',m.start())
  out[m[1]]=s[m.start():end].strip()
 return out
new,prior=definitions(raw),definitions(old)
port=json.loads((E/'extraction/shared-declarations.json').read_text())
for row in port['reused']:
 body=new[row['name']];assert body==prior[row['name']]
 assert hashlib.sha256(body.encode()).hexdigest()==row['sha256']
body=new['prover_commit_reference.collect_m31_owned']
adopted=Path('docs/research/v8-r0-zk-20261009/lean/AspisR1ProverCollect10/Funs.lean').read_text()
assert definitions(adopted)['prover_commit_reference.collect_m31_owned']==body
assert hashlib.sha256(body.encode()).hexdigest()==port['new_function_sha256']
for p,s in json.loads((E/'host-inputs.json').read_text())['files'].items():assert sha(Path(p))==s,p
assert json.loads((E/'host-inputs-checked.json').read_text())['all_matched']
for p in (E/'receipts').glob('*/receipt.json'):
 r=json.loads(p.read_text());assert r['exit_status']==r['swaps']==0,p
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},p
 assert r['peak_rss_kib']>0 and r['wall_seconds']>0
elf=json.loads((E/'frozen-elf-final-check.json').read_text())
for r in elf['programs'].values():assert r['cmp_exit']==0 and r['byte_identical'] and r['sha256']==r['expected_sha256']
allowed={'propext','Classical.choice','Quot.sound'}
for p in (E/'lean').glob('lean-*.json'):
 r=json.loads(p.read_text());a=r['attempt'];snap=E/'lean/sources'/f"attempt-{a}-{Path(r['module']).stem}.lean.txt"
 assert sha(snap)==r['source_sha256'],p
 assert hashlib.sha256(json.dumps(r['deps'],sort_keys=True).encode()).hexdigest()==r['deps_fingerprint'],p
 out=(E/'lean'/f'out-{a}.log').read_text();tm=(E/'lean'/f'time-{a}.log').read_text()
 assert re.search(r'^exit=(\d+)',out,re.M)
 if a in M['adopted_attempts']:
  assert re.search(r'^exit=0$',out,re.M),p
  source=Path('docs/research/v8-r0-zk-20261009/lean')/r['module'];assert sha(source)==r['source_sha256'],p
  lines=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.S)
  for line in lines:
   axioms=re.search(r'\[([^\]]*)\]',line)
   assert not axioms or set(axioms[1].split(', '))<=allowed,(p,line)
  assert 'Swaps: 0' in tm and 'error:' not in out and 'error(' not in out
if '--check' not in sys.argv:
 a=M['final_audit_attempt'];out=(E/'lean'/f'out-{a}.log').read_text()
 assert re.search(r'^exit=0$',out,re.M)
 lines=re.findall(r"'([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.S)
 assert len(lines)==M['final_audit_lines'],len(lines)
 assert [n for n,_ in lines]==M['axiom_targets']
 for n,line in lines:
  axioms=re.search(r'\[([^\]]*)\]',line)
  assert not axioms or set(axioms[1].split(', '))<=allowed,(n,line)
print('Validated frozen sources, extraction port, capped receipts, premise diff, ELF identities'+(' and final axioms audit' if '--check' not in sys.argv else ' (preflight)'))
