from pathlib import Path
import hashlib,json,lzma,re,shutil,os
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sourcepins=json.loads((B/'NJT_Q_SOURCE_PINS.json').read_text())
for name in ['NJT_Q_SOURCE_PINS.json','NJT_Q_FROZEN_FILE_PINS.json']:
 for n,h in json.loads((B/name).read_text()).items():assert sha(B/'NJT_Q_src'/n)==h,n
for name in ['NJT_QEXPORT.json','NJT_QCLAIMS_EXPORT.json']:
 for p in json.loads((B/name).read_text())['files']:assert sha(Path(p['path']))==p['sha256'],p['path']
t=(B/'NJT_Q_src/crates/aspis-core/src/r0_transcript.rs').read_text();start=t.index('fn block_rank(');end=t.index('\n/// Binary long division',start)
bodysha=hashlib.sha256(t[start:end].strip().encode()).hexdigest();assert bodysha==json.loads((B/'NJT_Q_REF_IDENTITY.json').read_text())['normalized_body_sha256']
assert sha(B/'NJT_Q_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
cases=[];features={};archives=[]
for num,want,kind,diagnostic in [(6,0,'weak first-cell contract positive',''),(7,1,'same contract inverted ensures','out[0] != NJT_Q_rank_ref'),(8,0,'unimplied second-cell assertion on real body',''),(9,1,'SAME caller under stub_verified','out[1] == NJT_Q_rank_ref'),(10,0,'local-record allowed-field modifies positive',''),(11,1,'SAME local-record contract with undeclared frame-field mutation','is assignable')]:
 a=f'NJT_QK{num:03}';r=json.loads((B/a/'receipt.json').read_text());log=(B/a/'stdout.log').read_text();assert r['exit_status']==want,(a,r['exit_status']);assert ('VERIFICATION:- SUCCESSFUL' if want==0 else 'VERIFICATION:- FAILED') in log,a
 assert 'timed out' not in log.lower(),a
 if diagnostic:assert diagnostic in log,a
 pins=json.loads((B/a/'sources/NJT_Q_SOURCE_PINS.json').read_text());assert pins==sourcepins,a
 g=B/(a+'-graph.json');meta=json.loads(g.read_text());nodes={p['id']:p for p in meta['resolve']['nodes']};features[a]=[dict(id=p['id'],name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in meta['packages']]
 gc=B/(a+'-graph-check.json');gl=json.loads(gc.read_text());lc=B/(a+'-lock-check.json');lock=json.loads(lc.read_text());assert gl['graph_matches_frozen'] is True and lock['unchanged'] is True,a
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_TARGET_DIR']==str(B/'NJT_Q_target'),a
 q=B/(a+'-graph.json.xz');q.write_bytes(lzma.compress(g.read_bytes(),preset=6));(B/(a+'-graph.json.sha256')).write_text(sha(g)+'\n');archives.append(dict(path=q.name,uncompressed_sha256=sha(g),compressed_sha256=sha(q)))
 cases.append(dict(attempt=a,kind=kind,expected_exit=want,actual_exit=r['exit_status'],target=r['module'],same_original_harness_name=True,source_revision=r['source_revision'],source_hashes=r['source_hashes'],core_source_sha256=pins['crates/aspis-core/src/r0_transcript.rs'],calibration_source_sha256=sha(B/'NJT_Q_array8_calibration.rs.txt'),rustflags=r['env']['RUSTFLAGS'],native_command=r['native_command'],receipt_sha256=sha(B/a/'receipt.json'),wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],limits=r['limits'],graph_check_sha256=sha(gc),metadata_sha256=sha(g),lock_check_sha256=sha(lc),lock=lock,failed_checks=re.findall(r'^Failed Checks: (.*)$',log,re.M),status='PASS_EXPECTED_VERDICT',print_axioms='N/A native fidelity fixture'))
for left,right in [(0,1),(2,3),(4,5)]:assert cases[left]['target']==cases[right]['target']
report=dict(status='PASS all three strict ruling(t) fixed-array8 fidelity controls',shape='borrowed fixed32-byte input -> owned [u32;8]; pure contract and local mutable record allowed-field footprint',cases=cases,actual068_inverted_control='NJT_QK005; actual068 positive NJT_QK004 retained unchanged',production_stub_verified_used=False,calibration_stub_verified_pair=['NJT_QK008','NJT_QK009'],no_new_lean_module=True,no_combined_audit_rerun=True,no_timeout_or_memory_kill=True,no_shape_repair_or_renaming=True,frozen_block_rank_normalized_body_sha256=bodysha,kmx_patch_sha256=sha(B/'NJT_Q_KMX.patch'),full_features='NJT_QSHAPE_FEATURES.json',metadata_archives=archives,cargo_target_dir=str(B/'NJT_Q_target'),trust='P6/D188 option-A fidelity evidence; no added/removed trust and no production source edit')
(B/'NJT_QSHAPE_FEATURES.json').write_text(json.dumps(features,indent=2));report['full_features_sha256']=sha(B/'NJT_QSHAPE_FEATURES.json');(B/'NJT_QSHAPE_FIDELITY.json').write_text(json.dumps(report,indent=2))
free=lambda:os.statvfs(B).f_bavail*os.statvfs(B).f_frsize
before=free();removed=[]
for name in ['NJT_Q_target','NJT_Q_tmp']:
 p=B/name;assert p.parent==B and not p.is_symlink()
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
(B/'NJT_QSHAPE_FINAL_HOST.json').write_text(json.dumps(dict(removed_rebuildable_outputs=removed,free_bytes_before=before,free_bytes_after=free(),retained_exports_verified=True,final_source_manifests_verified=True,frozen_lock_unchanged=True,cache_deleted=False,keys_touched=False,cargo_target_dir=str(B/'NJT_Q_target')),indent=2));print('strict array8 fidelity PASS; source/feature/lock pins retained; own target/temp cleaned')
