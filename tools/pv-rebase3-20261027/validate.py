"""Validate committed receipt consistency; does not rerun any native/formal gate."""
import pathlib,json,hashlib
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-rebase3-20261027'
def read(p):return json.loads((E/p).read_text())
elf=read('elf-gate.json');assert elf['passed'] and len(elf['builds'])==3
for x in elf['builds']:assert x['matches'] and x['sha256']==x['expected'] and x['exit_status']==0
fixtures=read('fixture-comparison.json');assert fixtures['passed']
assert fixtures['revisions']['research']=='237e13556180d2ce0320a2760f89b35b5f4f02bb'
assert fixtures['revisions']['candidate']=='37794d7bff003fe396b43eb6e264bd9b29f40575'
for x in fixtures['comparisons']:
 assert all(x['returned_fields_equal'].values())
 for f in x['files'].values():assert f['byte_identical'] and f['research_sha256']==f['candidate_sha256']
 for row in x['records'].values():assert row['status']=='Ok' and row['attempts']==row['callbacks']==1
route=read('binary-route/meta.json');expected='9ac299ded6ef01aa4fa16d6ff3ad20a74c3e816c88040b5f9b5fdb57fc9c4d84';assert route['binary_sha256']==expected
assert read('candidate/build-devnet/binary-pins.json')['devnet_spend']['sha256']==expected
symbols=read('binary-route/route-symbols.json');assert any('generate_for_mask_nonce' in x['symbol'] and x['resolved_reachable'] and len(x['path'])==4 for x in symbols)
assert not any('StateOnlyAttemptSecrets::generate' in x['symbol'] and 'generate_for_mask_nonce' not in x['symbol'] and x['resolved_reachable'] for x in symbols)
source=read('source-route.json');assert sum(x['matches_pinned_client'] for x in source['files'])==6
for x in read('source-verification.json')['snapshots']:assert not x['mismatches']
rows=[]
for p in sorted(E.glob('**/receipt/receipt.json')):
 r=json.loads(p.read_text());assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['peak_rss_kib'] is not None and r['swaps']==0 and r['print_axioms']=='N/A: no Lean compilation'
 expected_exit=1 if p.relative_to(E).as_posix()=='candidate/build-default/receipt/receipt.json' else 0
 assert r['exit_status']==expected_exit,(p,r)
 rows.append(dict(receipt=str(p.relative_to(E)),**{k:r[k] for k in ['source_revision','command','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','limits','print_axioms']}))
assert len(rows)==10,len(rows)
(E/'resource-summary.json').write_text(json.dumps(dict(scopes=rows,one_scope_at_a_time=True,lean_attempts=0,lean_budget=30,kani_attempts=0,kani_budget=0,reason_no_lean='No existing Lean source or extracted prover/verifier body changed; re-validation inventory requested, not an unchanged replay. Shared env-J sources and objects were never written.',no_differential_or_timing_gate=True),indent=2)+'\n')
assert len(read('key-retention.json')['keys'])==3
for k in read('key-retention.json')['keys']:assert k['mode']=='0o600'
assert not read('cleanup.json')['retained_targets']
for f in E.rglob('*'):
 assert not f.is_file() or f.suffix not in ['.so','.olean','.rlib','.bin'],f
print('PASS: ELF pins, actual client binary/route, both fixtures, ten capped scopes, source manifests and retained-key policy')
