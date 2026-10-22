from pathlib import Path
import hashlib,json,sys
live = "--live-objects" in sys.argv
root=Path(__file__).resolve().parent
e=root/'evidence'
m=json.loads((e/'manifest.json').read_text())
r=json.loads((e/'complete-replay.json').read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(root/'sources/AspisR1CurrentCaller/Types.lean')==m['source_snapshot']['adapted_sha256']
assert sha(root/'sources/CallerImportCompatibilityFull.lean')==m['combined_import_probe']['source_sha256']
assert r['source_revision_at_launch']==m['launch_git_revision']
assert r['compiler_sha256']==m['compiler_sha256']
assert hashlib.sha256(r['lean_path'].encode()).hexdigest()==r['lean_path_sha256']
assert r['lean_path']==(e/'effective-LEAN_PATH.txt').read_text().strip()
assert r['lean_path_sha256']==m['combined_import_probe']['effective_path_sha256']
assert len(r['targets'])==7
for x in r['targets']:
    assert x['exit_status']==0 and x['source_sha256_before']==x['source_sha256_after']
    assert x['swaps_time_l']==0 and x['max_process_rss_bytes_time_l']>0
    assert x['max_aggregate_rss_bytes_sampled']>0
    assert x['source_revision_at_launch']==r['source_revision_at_launch']
    assert (e/Path(x['time_log']).name).is_file() and (e/Path(x['stdout_log']).name).is_file()
    if live: assert sha(x['object'])==x['object_sha256']
assert r['targets'][-1]['object_sha256']
assert all(v['inverse_transform_check']=='PASS' for v in [json.loads((e/'adapter-check.json').read_text())])
for mod,pin in m['selected_import_object_pins'].items():
    if live:
        assert Path(pin['path']).is_file(),mod
        assert sha(pin['path'])==pin['sha256'],mod
assert 'propext' in (e/'CallerImportCompatibilityFull.replay.log').read_text()
assert 'Classical.choice' in (e/'CallerImportCompatibilityFull.replay.log').read_text()
assert 'Quot.sound' in (e/'CallerImportCompatibilityFull.replay.log').read_text()
for p in root.rglob('*.olean'):
    assert 'objects' in p.parts, p
print('packet source/evidence checks PASS; local OLean outputs are excluded from packet')
