"""Read-only final binding, key retention and evidence audit; no gate replay."""
from pathlib import Path
import hashlib,json,stat,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');O=H/'bundle';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected=json.loads((O/'expected-sources.json').read_text());bad=[]
for p,h in expected.items():
 q=H/'src'/p
 if not q.is_file() or sha(q)!=h:bad.append(dict(path=p,expected=h,actual=sha(q) if q.is_file() else None))
assert not bad,bad
build=json.loads((O/'client-build.json').read_text());assert sha(H/'native-target/client/devnet_spend')==build['sha256']
elfs=[]
for mode,folder,name,pin in [('default','elf-default-affinity4','aspis_r1_cost_probe_program.so','f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4'),('devnet','elf-devnet','aspis_r1_cost_probe_program.so','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299'),('pool','elf-pool','aspis_pool.so','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')]:
 p=O/folder/name;ref=Path('/home/dombarker/project-offloads/codex-pv-client-20261026/artifacts')/(mode+'.so')
 assert sha(p)==pin and sha(ref)==pin and p.read_bytes()==ref.read_bytes()
 elfs.append(dict(mode=mode,sha256=pin,bytes=p.stat().st_size,literal_byte_comparison=True))
g=json.loads((O/'client-unit-graph.json').read_text());assert len(g['roots'])==1 and g['units'][g['roots'][0]]['target']['name']=='devnet_spend'
assert all('insecure-spend-fixture' not in u['features'] for u in g['units'])
assert any('aspis-r1-cost-probe' in u['pkg_id'] and 'ct-host-prover' in u['features'] for u in g['units'])
assert json.loads((O/'ct-decoding.json').read_text())['identical']
assert json.loads((O/'signing-fixture.json').read_text())['byte_identical']
assert json.loads((O/'fixed-fixture-comparison.json').read_text())['passed']
a=json.loads((O/'runtime-private/acceptance.json').read_text());assert len(a['runs'])==4 and all(r['accepted'] and r['duplicate_ledger_unchanged'] for r in a['runs'])
c=json.loads((O/'corpus-6000/pipeline-final.json').read_text());assert c['complete'] and c['passed'] and c['completed_pairs']==1000
assert json.loads((O/'corpus-ledger-audit.json').read_text())['passed']
t=json.loads((O/'timing/summary.json').read_text());assert len(t['summary'])==2 and all(r['verdict']=='PASS' for r in t['summary'])
assert sha(H/'artifacts/baseline-devnet_spend')=='30d883a8d97f12c315898aaf9170eb7a542b5e935881f089506fd4601ddb6a20'
keys=[]
for folder in [O/'runtime-private',*(O/x for x in ['elf-default-affinity4','elf-devnet','elf-pool'])]:
 for p in folder.rglob('*'):
  if p.is_file() and (p.suffix=='.key' or p.name.endswith('keypair.json')):
   # Retain securely; never inventory/export secret values or destroy keys.
   p.chmod(0o600);keys.append(dict(path=str(p),bytes=p.stat().st_size,mode=oct(stat.S_IMODE(p.stat().st_mode)),disposition='retained securely; no key cleanup authorized; no on-chain balances or authorities touched'))
fixture=O/'RFC8032-public-fixture-key.json';assert fixture.exists() and stat.S_IMODE(fixture.stat().st_mode)==0o600
r=dict(source_files_checked=len(expected),source_mismatches=bad,production_source_freeze='ba39168f67',client=build,elfs=elfs,gate_checks_passed=True,retained_keys=keys,public_RFC8032_key_retained=True,keys_deleted=0,release_pins_changed=False,print_axioms='N/A; no Lean or Kani',baseline_client_sha256=sha(H/'artifacts/baseline-devnet_spend'),corpus_resources=c['final_resources'])
(O/'final-audit.json').write_text(json.dumps(r,indent=2)+'\n');print('FINAL_SOURCE_ARTIFACT_GATE_KEY_RETENTION_AUDIT_PASS',flush=True)
