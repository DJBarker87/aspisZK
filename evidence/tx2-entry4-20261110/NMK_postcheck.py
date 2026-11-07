from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
snapshots=0;receipts=0;ae={}
for p in sorted(B.glob('NMK_[KL][0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text());receipts+=1
 ad=json.loads((B/(x['attempt']+'-reservation.json')).read_text());assert ad['allowed'] is True,x['attempt']
 for name,h in x['source_hashes'].items():
  q=p.parent/'sources'/name;assert q.is_file() and sha(q)==h,str(q);snapshots+=1
 for path,row in x['deps_fingerprint']['selected_objects'].items():
  if 'Aeneas' not in path:continue
  if path in ae:assert ae[path]==row['sha256'],path
  ae[path]=row['sha256']
for path,h in ae.items():assert sha(Path(path))==h,path
assert sha(B/'NMK_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
export=json.loads((B/'NMK_EXPORT.json').read_text())
for row in export['files']:assert sha(Path(row['path']))==row['sha256']
ret=json.loads((B/'NMK_RETENTION.json').read_text());workspace=sum(p.stat().st_size for p in B.rglob('*') if p.is_file() and not p.is_symlink());assert workspace<30_000_000_000
ret.update(workspace_bytes=workspace,free_bytes=shutil.disk_usage(B).free,completed_receipts_checked=receipts,source_snapshots_checked=snapshots,all_source_snapshots_match=True,aeneas_unique_objects_checked=len(ae),all_aeneas_pins_stable_across_scopes=True,all_export_files_unchanged=True)
(B/'NMK_RETENTION.json').write_text(json.dumps(ret,indent=1)+'\n')
tools=json.loads((B/'NMK_TOOL_PINS.json').read_text())
for p in [B/'NMK_native/NMK_ScanDriver',B/'S2W_run_host.py']:
 tools[str(p)]=dict(sha256=sha(p),bytes=p.stat().st_size)
(B/'NMK_TOOL_PINS.json').write_text(json.dumps(tools,indent=1)+'\n')
print(json.dumps(dict(receipts=receipts,snapshots=snapshots,aeneas=len(ae),workspace_bytes=workspace,export_unchanged=True)))
