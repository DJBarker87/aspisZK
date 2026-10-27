"""Read-only verification of retained ELF replay receipts; no build."""
import json,hashlib,pathlib
P=pathlib.Path(__file__).resolve().parent;R=P.parents[1]
x=json.loads((P/'ELa_build_manifest.json').read_text())
pins={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
assert len(x['builds'])==3 and x['scope_count']==1
scopes=set()
for b in x['builds']:
 assert b['exit_status']==0 and b['sha256']==b['expected_sha256']==pins[b['mode']] and b['byte_identical']
 assert b['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert b['swaps']=='0' and not any(k.startswith('CARGO_PROFILE_') for k in b['env'])
 scopes.add(b['cgroup'])
 for f,pin in b['log_pins'].items():
  p=P/('ELa_'+b['mode'])/f;assert p.stat().st_size==pin['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==pin['sha256']
 for inv in b['compiler_invocations']:assert '-C' in inv['args'] and 'opt-level=3' in inv['args']
assert len(scopes)==1
assert x['postbuild_source_census']=={'checked':1243,'mismatches':[]}
assert x['repository_compiler_inputs']=={'checked':157,'mismatches':[]}
h=json.loads((R/'evidence/lowering2-20261026/Low2_build_manifest.json').read_text())
inputs={f['path']:f['sha256'] for b in h['builds'] for f in b['repository_compiler_inputs']}
assert all(hashlib.sha256((R/p).read_bytes()).hexdigest()==s for p,s in inputs.items())
d=json.loads((P/'ELa_source_diff.json').read_text());assert not d['changed_shipped_files'] and not d['build_config_diff'] and not d['shipped_commits']
print('PASS: three frozen pins, one capped scope, raw receipt hashes, 157 compiler inputs, no shipped drift')
