from pathlib import Path
import json,hashlib,subprocess,re,collections
E=Path(__file__).resolve().parent
ledger=[json.loads(s) for s in (E/'KNH_ATTEMPTS.jsonl').read_text().splitlines()]
runs=[r for r in ledger if r['kind']=='kani']
assert len(runs)==50
assert collections.Counter(r['tool_version'] for r in runs)=={'new':40,'old':10}
assert len({r['attempt'] for r in ledger})==len(ledger)
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
source_pins={hashlib.sha256(p.read_bytes()).hexdigest():p.name for p in E.glob('KNH_*.rs.txt')}
preflight_gap=[]
for r in ledger:
 assert r['limits']==limits and r['swaps']=='0'
 assert (E/(r['attempt']+'-reservation.json')).is_file()
 assert json.loads((E/(r['attempt']+'-reservation.json')).read_text())['allowed'] is True
 assert json.loads((E/r['attempt']/'receipt.json').read_text())==r
 assert r['source_revision'] and r['source_hashes'] and r['print_axioms'].startswith('N/A:')
 if r['kind']!='kani':continue
 assert r['source_hashes']['KNH_scratch/KNH_probe.rs'] in source_pins,r['attempt']
 assert r['source_hashes']['KNH_scratch/KMX_stubs.rs']==hashlib.sha256((E/'KNH_KMX_stubs.rs.txt').read_bytes()).hexdigest()
 assert r['env']['CARGO_NET_OFFLINE']=='true'
 check=json.loads((E/(r['attempt']+'-graph-check.json')).read_text())
 assert check['lock_unchanged'] and check['lock_before_sha256']==check['lock_after_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 strict=E/(r['attempt']+'-strict-graph.json')
 if strict.exists():
  s=json.loads(strict.read_text());assert s['exact_frozen_graph_match'] and len(s['resolved_features'])==441
  assert s['lock_before']==s['lock_after']==s['scratch_lock_after']==check['lock_after_sha256']
 else:preflight_gap.append(r['attempt'])
assert preflight_gap==[f'KNH_N{i:03d}' for i in range(1,20)]
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text().split('diff --git a/KMX_native.rs')[0]
payload='\n'.join(l[1:] for l in patch.splitlines() if l.startswith('+') and not l.startswith('+++'))+'\n'
assert (E/'KNH_KMX_stubs.rs.txt').read_text()==payload
before=json.loads((E/'KNH_PINNED_BEFORE.json').read_text())['files'];after=json.loads((E/'KNH_CLEANUP.json').read_text());assert before==after['pinned_tools']
assert after['cache_unchanged'] and after['installation_unchanged'] and not after['live_own_provers']
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
base='f2219bb23f^'
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert all(p.startswith('evidence/kani-sandbox-20261028/') for p in changed),changed
out=dict(receipts=len(ledger),kani_invocations=len(runs),new=40,pinned=10,lean=0,all_limits_exact=True,all_swaps_zero=True,all_admissions_allowed=True,all_probe_sources_archived_by_hash=True,approved_copy_payload_exact=True,all_scratch_locks_unchanged=True,strict_preflight_count=31,preflight_noncompliance=preflight_gap,tool_and_cache_hashes_unchanged=True,modified_paths_confined=True,max_evidence_bytes=max(p.stat().st_size for p in E.rglob('*') if p.is_file()),peak_rss_kib=max(int(r['peak_rss_kib']) for r in ledger),total_kani_wall_seconds=sum(r['wall_seconds'] for r in runs),no_new_credit=True)
(E/'KNH_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
