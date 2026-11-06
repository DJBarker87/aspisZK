from pathlib import Path
import json,shutil,hashlib
B=Path(__file__).resolve().parent;v=json.loads((B/'NJT_FINAL_HOST_VALIDATION.json').read_text());assert v['status']=='PASS'
export=json.loads((B/'NJT_EXPORT.json').read_text())
for r in export['files']:assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256']
removed=[];before=shutil.disk_usage(B).free
for name in ['NJT_objects','NJT_native','NJT_tmp']:
 p=B/name;assert p.parent.resolve()==B.resolve() and not p.is_symlink()
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
report=dict(status='PASS',removed=removed,export_retained=export['directory'],free_before=before,free_after=shutil.disk_usage(B).free,keys_created=False,key_operations=False,cargo_target_dir=str(B/'NJT_target'),note='Only owned rebuildable compiled-object/audit-native/temp outputs; all retained caches, sources, receipts and exports preserved')
(B/'NJT_CLEAN_OBJECTS.json').write_text(json.dumps(report,indent=2)+'\n')
print('NJT owned rebuildable outputs removed; retained export hashes match')
