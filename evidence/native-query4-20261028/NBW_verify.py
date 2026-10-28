from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
hashes={}
for patch in ['NBW_controls_source.patch','NBW_replay_v1.patch','NBW_replay_v2.patch','NBW_harness.patch']:
 s=(E/patch).read_text().split('+++ b/crates/aspis-r1-cost-probe/src/NBW_native.rs\n',1)[1].split('--- ',1)[0]
 src=''.join(l[1:] for l in s.splitlines(keepends=True) if l.startswith('+'))
 hashes[hashlib.sha256(src.encode()).hexdigest()]=patch
kmxpatch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
s=kmxpatch.split('+++ b/KMX_stubs.rs\n',1)[1].split('diff --git',1)[0]
kmx=''.join(l[1:] for l in s.splitlines(keepends=True) if l.startswith('+'))
kmxhash=hashlib.sha256(kmx.encode()).hexdigest()
errors=[];rows=[]
for p in sorted(E.glob('NBW_K*/receipt.json')):
 rc=json.loads(p.read_text());a=rc['attempt'];cfg=json.loads((E/(a+'.json')).read_text());graph=json.loads((E/(a+'-graph-check.json')).read_text())
 assert graph['exact_frozen_resolved_graph_match'] and graph['lock_unchanged'],a
 assert graph['lock_before_sha256']==graph['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
 assert cfg['env']['CARGO_NET_OFFLINE']=='true',a
 assert cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
 module=rc['source_hashes']['NBW_src/crates/aspis-r1-cost-probe/src/NBW_native.rs']
 assert module in hashes,(a,module)
 assert rc['source_hashes']['NBW_src/crates/aspis-r1-cost-probe/src/KMX_stubs.rs']==kmxhash,a
 assert int(rc['swaps'])==0,a
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},(a,rc['limits'])
 rows.append(dict(attempt=a,patch=hashes[module],source_sha256=module,exit=rc['exit_status']))
assert len(rows)==50,len(rows)
for p in E.glob('NBW_L*/receipt.json'):
 rc=json.loads(p.read_text())
 if rc['exit_status']==0:
  assert all('sorryAx' not in x and '[adjacent]' not in x for x in rc['print_axioms']),p
(E/'NBW_VERIFICATION.json').write_text(json.dumps(dict(errors=errors,kani_source_versions=rows,all_frozen_graphs_and_locks_valid=True,all_scopes_capped=True,exact_kmx_stub_payload_sha256=kmxhash),indent=2)+'\n')
print('50 native configurations verified; source versions, frozen graphs/locks, offline optimized profile, exact KMX payload and resource caps match')
