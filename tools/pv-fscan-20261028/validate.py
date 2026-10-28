from pathlib import Path
import json,lzma,hashlib,subprocess,tomllib,re
E=Path('evidence/pv-fscan-20261028');a=json.loads((E/'scan.json').read_text());checks={}
assert str(Path.cwd())==a['worktree'];assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()==a['branch'];subprocess.run(['git','merge-base','--is-ancestor',a['source_revision'],'HEAD'],check=True)
checks['exact_worktree_branch_and_candidate_ancestor']=True
rows={r['id']:r for r in a['rows']};selected=json.loads((E/'selected-rows.json').read_text());assert len(rows)==len(selected)==66 and set(rows)=={r['id'] for r in selected}
assert sum(r['prior_status']=='CLOSED-ON-CANDIDATE' for r in selected)==53
assert {i for i,r in rows.items() if r['status']=='SUSPENDED'}==set(a['summary']['measured_difference_rows'])|set(a['summary']['undetermined_rows'])
for r in a['rows']:
 if r['status']=='STANDS':assert not r['matched_changed_bodies'] and r['unresolved_edge_count']==0
 else:assert r['matched_changed_bodies'] or r['unmatched_function_identities'] or r['unresolved_edge_count'] or r.get('concrete_probe')
assert a['summary']['feature_only_changed_rows']==[]
checks['all_rows_dispositioned_without_unknown_credit']=True
units=json.loads((E/'artifacts/units-client-bin/features.json').read_text());libs=json.loads((E/'artifacts/libraries-client194-exact/mir-manifest.json').read_text())
for name,version in [('sha2','0.10.9'),('digest','0.10.7'),('block-buffer','0.10.4'),('zeroize','1.9.0'),('generic-array','0.14.7'),('typenum','1.20.1'),('crypto-common','0.1.7'),('subtle','2.6.1')]:
 expected=[u for u in units if u['name']==name and u['package_id'].endswith('@'+version)];actual=[u for u in libs if u['package_id'].endswith('#'+name+'@'+version)];assert len(actual)==1 and expected,(name,actual)
 assert any(set(v['features'])==set(actual[0]['features']) for v in expected),(name,actual[0]['features'],expected)
checks['exact_client_dependency_versions_and_features']=True
for n in ['default','devnet']:
 u=json.loads((E/f'artifacts/units-{n}/features.json').read_text());p=next(x for x in u if x['name']=='aspis-statement');assert len(set(p['features'])-{'r0','pool-v1-kernel'})==12
 p=next(x for x in u if x['name']=='aspis-r1-cost-probe');assert set(p['features'])=={'default','optimized-terminal','private-leaf-salts','program-build'}
 assert p['platform']=='sbpf-solana-solana' and not p['profile']['overflow_checks'] and not p['profile']['debug_assertions']
checks['three_elf_feature_graphs_and_release_profiles']=True
assert a['budgets']['native_scopes_used']<=150 and a['budgets']['kani_verification_runs']==a['budgets']['lean_attempts']==0 and not a['budgets']['env_j_ids_used']
for p in E.glob('*/receipt.json'):
 r=json.loads(p.read_text());assert r['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64);assert str(r['swap'])=='0';assert r['target'] and r['wall'] and r['peak_rss_kib'] and re.fullmatch('[0-9a-f]{40}',r['source_revision']);assert r.get('axioms','').startswith('N/A')
 for n in ['admission-before.json','admission-barrier.json']:assert json.loads((p.parent/n).read_text())['allowed'] is True
checks['serial_capped_receipts_and_zero_provers']=True
# Stream decompression keeps local inspection memory small; do not materialize entire MIR corpora.
manifest=json.loads((E/'dump-manifest.json').read_text());verified={}
for r in manifest:
 p=E/'artifacts'/r['compressed']
 if str(p) not in verified:
  h=hashlib.sha256();size=0
  with lzma.open(p,'rb') as f:
   while b:=f.read(1024*1024):h.update(b);size+=len(b)
  verified[str(p)]=(h.hexdigest(),size)
 assert verified[str(p)]==(r['sha256'],r['size']),r['path']
checks['retained_mir_sha256_and_size']=dict(snapshots=len(manifest),unique_files=len(verified))
cleanup=json.loads((E/'cleanup.json').read_text());assert cleanup['runtime_files_verified']==517 and not cleanup['source_mismatches'] and not cleanup['live_own_compilers'];assert cleanup['removed_rebuildable_targets']
assert 'e408947bfd200af42db322daf0fadfe7e26d3bd1' in cleanup['tool_versions']['1.94.1']['rustc']
checks['runtime_source_identity_toolchain_and_cleanup']=True
cfg=tomllib.loads(Path('.cargo/config.toml').read_text());assert set(cfg)=={'alias'}
changed=subprocess.check_output(['git','diff','--name-only',a['source_revision']],text=True).splitlines();new=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines();assert all(p.startswith(('evidence/pv-fscan-20261028/','tools/pv-fscan-20261028/')) for p in changed+new)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
subprocess.run(['git','diff','--check'],check=True)
checks['path_limited_no_runtime_changes_size_and_whitespace']=True
out=dict(status='PASS',checks=checks,revision_before_final_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),summary=a['summary'],budgets=a['budgets'],scope='Evidence-integrity and classification validation, not a Lean/native semantic proof')
(E/'validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status='PASS',checks=list(checks),budgets=a['budgets'])))
