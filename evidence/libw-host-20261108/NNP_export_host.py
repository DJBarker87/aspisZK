"""Pin the selected closure; retain exports; remove only this job's scratch copies."""
from pathlib import Path
import json,hashlib,shutil,lzma
B=Path.cwd();assert json.loads((B/'NNP_L016/receipt.json').read_text())['exit_status']==0
assert 'NNP_FINAL_ALL_CHECKS_PASSED' in (B/'NNP_L016/stdout.log').read_text()
roots=json.loads((B/'NNP_L016/receipt.json').read_text())['env']['LEAN_PATH'].split(':')
rows=[json.loads(l) for l in (B/'NNP_LOADED_scan.jsonl').read_text().splitlines()]
exports=B/'NNP_exports_20261108';exports.mkdir(exist_ok=False);pins=[];imported=[]
for row in rows:
 rel=row['module'].replace('.','/')+'.olean'
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 assert p is not None,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  record=dict(module=row['module'],path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size)
  pins.append(record)
  if str(z).startswith(str(B)+'/'):
   # All copied inputs are retained with provenance; external caches stay read-only.
   source_root=next(root for root in roots if str(z).startswith(root+'/'))
   dst=exports/z.relative_to(source_root);dst.parent.mkdir(exist_ok=True,parents=True)
   shutil.copy2(z,dst)
   record['export_path']=str(dst)
   origins={'NNP_seedLIBB':'/home/dombarker/project-offloads/codex-cx-libb-20261111/LIBB_objects','NNP_seedNNH':'/home/dombarker/project-offloads/codex-cx-integrate-20261111/NNH_objects','NNP_seedNNH_R4':'/home/dombarker/project-offloads/codex-cx-integrate-20261111/NNH_R4_objects'}
   record['copied_from']=str(Path(origins[Path(source_root).name])/z.relative_to(source_root)) if Path(source_root).name in origins else 'compiled by NNP; see scope receipt'
   imported.append(record)
# Keep the small validation utility object as a recorded, non-proof export too.
for z in (B/'NNP_objects').glob('NNP_Scan.*'):
 if z.is_file():shutil.copy2(z,exports/z.name)
raw=json.dumps(pins,sort_keys=True,indent=1).encode();(B/'NNP_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NNP_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(B/'NNP_IMPORTED_HASHES.json').write_text(json.dumps(imported,indent=1)+'\n')
exported=[dict(path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size) for z in sorted(exports.rglob('*')) if z.is_file()]
(B/'NNP_EXPORT.json').write_text(json.dumps(dict(export_directory=str(exports),objects=exported,modules=len(rows),prepend_to='LIBB_L344 LEAN_PATH; selected NNH supplement objects are included in export'),indent=1)+'\n')
# Remove only known, job-owned scratch paths. Preserve all attempt receipts and export.
removed=[]
for name in ['NNP_seedLIBB','NNP_seedNNH','NNP_seedNNH_R4','NNP_generated','NNP_objects','NNP_native','NNP_tmp']:
 p=B/name
 if p.is_dir():shutil.rmtree(p);removed.append(str(p))
p=B/'NNP_ProofDriver'
if p.is_file():p.unlink();removed.append(str(p))
(B/'NNP_CLEANUP.json').write_text(json.dumps(dict(removed=removed,retained_export=str(exports),shared_caches_touched=False),indent=1)+'\n')
print(json.dumps(dict(export=str(exports),objects=len(exported),closure_modules=len(rows),removed=len(removed))))
