from pathlib import Path
import hashlib,json,lzma,subprocess,re
E=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
base='1d7752908191642fc8383c99bbadfb46fab8850c'
rows=[json.loads(l) for l in (E/'NCY_ATTEMPTS.jsonl').read_text().splitlines()]
scopes=[r for r in rows if 'scope_command' in r]
assert len(scopes)==3
assert all(r['exit_status']==0 and r['admission_allowed'] and r['admission_exit']==0 and r['swaps']==0 for r in scopes)
for r in scopes:
 label=r['attempt'];assert sha((E/(label+'.py')).read_bytes())==r['source_sha256']
 reservation=json.loads((E/(label+'-reservation.json')).read_text());assert reservation['allowed'] is True
 assert all(s in r['scope_command'] for s in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64'])
for label,expected in [('NCY_B001','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299'),('NCY_B002','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')]:
 receipt=json.loads((E/(label+'-receipt.json')).read_text());a=receipt['result']
 assert a['artifact_sha256']==expected and a['match'] and a['build_exit']==0
 assert a['source_check_after']=={'files':1243,'mismatches':[]}
 assert a['cgroup_swap_peak_bytes']=='0'
 assert all(k['mode']=='0o600' and k['retained'] for k in a['keys'])
provenance=json.loads((E/'NCY_PROVENANCE.json').read_text())
for mode,m in provenance['cache_seed_manifests'].items():
 assert sha((E/Path(m['path']).name).read_bytes())==m['sha256']
index=json.loads((E/'NCY_COMPILER_SNAPSHOTS_INDEX.json').read_text());combined={}
for p in index['parts']:
 compressed=(E/p['path']).read_bytes();assert sha(compressed)==p['compressed_sha256']
 raw=lzma.decompress(compressed);assert sha(raw)==p['uncompressed_sha256']
 d=json.loads(raw);combined.update(d)
 side=E/p['path'].replace('.xz','.sha256');assert side.read_text().split()[0]==sha(raw)
assert sha((json.dumps(combined)+'\n').encode())==index['original_uncompressed_sha256']
for label,record in provenance['builds'].items():
 for p in record['diagnostics']:
  relative=str(Path(p['path']).relative_to(Path('/home/dombarker/project-offloads/codex-cx-native-elfpins-20261028')/label))
  assert sha(combined[label][relative].encode())==p['sha256']
 assert record['own_target_removed'].endswith(('NCY_target_devnet','NCY_target_pool'))
# Root statement identity check is static reuse, no Lean invocation.
root=Path('evidence/replay-deployed2-20261027/RPx_Deployed.kernel.lean.txt')
assert sha(root.read_bytes())=='8ae0107f9dbb7374135912ff9dda3597ad0096023d0deed471b0cd4dcf305523'
assert all(p.stat().st_size<20*1024*1024 for p in E.iterdir() if p.is_file())
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert all(p.startswith('evidence/native-elfpins-20261028/NCY_') for p in changed)
for n in ['NCY_ELF_REPRODUCTIONS.md','NCY_DEPLOYMENT_ROWS.md','NCY_TRUST_INVENTORY_DRAFT.md','NCY_HANDOFF.md']:
 assert (E/n).exists()
table=(E/'NCY_TRUST_INVENTORY_DRAFT.md').read_text();assert sum(l.startswith('| ') for l in table.splitlines())==57
subprocess.run(['git','diff','--check'],check=True)
result={'status':'pass','kind':'static artifact/receipt/source-scope and compressed-log validation; no prover replay','scope_count':len(scopes),'lean':0,'kani':0,'root_statement_sha256':sha(root.read_bytes()),'script_sha256':sha(Path(__file__).read_bytes()),'checked_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'limits':'6G/8G/Swap0/Tasks64','print_axioms':'N/A new theorem; reused RPx standard-only audit','changed_paths':changed}
(E/'NCY_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='changed_paths'},indent=2))
