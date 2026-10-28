"""Read-only final audit. No prover replay and no shipped-source mutation."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];D=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda data:hashlib.sha256(data).hexdigest()
rows=json.loads((E/'NBI_ATTEMPTS.json').read_text())['rows']
assert len([r for r in rows if r['kind']=='kani'])==30
assert len([r for r in rows if r['kind']=='lean'])==24
# Every harness source snapshot is one retained external patch version.
versions={}
for p in E.glob('NBI_harness*.patch'):
 text=p.read_text();file=None;addition=[]
 for line in text.splitlines(True)+['--- END\n']:
  if line.startswith('--- '):
   if file is not None and file.endswith(('NBI_keys.rs','NBI_multiproof.rs')):
    versions.setdefault(file,set()).add(sha(''.join(addition).encode()))
   file=None;addition=[]
  elif line.startswith('+++ b/'):file=line[6:].strip()
  elif file and line.startswith('+'):addition.append(line[1:])
 for _ in [0]:subprocess.run(['git','apply','--check',str(p)],cwd=R,check=True)
source_files=list(D.glob('NBI_*.lean'))
lean_hashes={sha(p.read_bytes()) for p in source_files}
lean_hashes.update(sha(p.read_bytes()) for p in E.glob('NBI_L*.source.lean.txt'))
for r in rows:
 for name,digest in r['source_hashes'].items():
  if name.endswith('.lean'):assert digest in lean_hashes,(r['attempt'],name,'missing Lean snapshot')
  if name.endswith(('NBI_keys.rs','NBI_multiproof.rs')):
   rel=name.removeprefix('NBI_src/');assert digest in versions[rel],(r['attempt'],name,'missing patch snapshot')
 if r['kind']=='kani':
  g=json.loads((E/(r['attempt']+'-graph.json')).read_text())
  assert g['allowed'] and not g['new_packages'] and not g['edge_errors'] and g['unchanged']
  assert g['lock_before']==g['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert g['resolved_packages']==441 and g['frozen_packages']==444
 receipt=json.loads((E/r['attempt']/'receipt.json').read_text())
 assert receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert receipt['swaps']=='0'
 ad=json.loads((E/(r['attempt']+'-reservation.json')).read_text());assert ad['allowed'] is True
 if r['kind']=='lean' and r['exit_status']==0:
  for line in r['print_axioms']:
   names=line.split('axioms: [')[-1].rstrip(']').split(', ') if 'axioms: [' in line else []
   assert set(names)<={'propext','Classical.choice','Quot.sound'}
for p in source_files:
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
roots=json.loads((E/'NBI_THEOREM_ROOTS.json').read_text())['roots']
audit=json.loads((E/'NBI_L024/receipt.json').read_text());assert audit['exit_status']==0
assert {s.split("'")[1] for s in audit['print_axioms']}==set(roots)
initial=json.loads((E/'NBI_INITIAL_HOST_PINS.json').read_text());terminal=json.loads((E/'NBI_TERMINAL_HOST.json').read_text())
for k in ['cache','coherent','aeneas']:
 assert all(terminal[k].get(p)==v for p,v in initial[k].items())
assert all(terminal['tools'].get(p)==v for p,v in initial['tools'].items())
assert terminal['frozen_sources_equal'] and terminal['frozen_file_count']==498
assert not terminal['live_owned_builds'] and not terminal['private_objects']
changed=subprocess.check_output(['git','diff','--name-only','7dc3c3e335fce86fd240e5f40b9c60adac9a68b0','--'],cwd=R,text=True).splitlines()
assert all(n.startswith('evidence/native-tx1b-20261027/') or n.startswith('docs/research/100bit-spend-path-20261013/lean/NBI_') for n in changed),changed
out=dict(all_checks_passed=True,lean_attempts=24,kani_runs=30,accepted_new_roots=len(roots),frozen_file_count=498,initial_cache_objects=len(initial['cache']),terminal_cache_objects=len(terminal['cache']),unchanged_coherent_objects=len(initial['coherent']),unchanged_aeneas_objects=len(initial['aeneas']),patches_apply=True,snapshot_hashes_covered=True,all_graphs_frozen=True,all_standard_axioms=True,all_scopes_terminal=True,persistent_cache_retained=True,shipped_files_unchanged=True)
(E/'NBI_STATIC_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
