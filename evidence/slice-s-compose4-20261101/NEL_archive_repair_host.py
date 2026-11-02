from pathlib import Path
import json,hashlib,shutil
b=Path(__file__).resolve().parent
old=json.loads((b/'NEL_CACHE_FINAL.json').read_text())
src=Path(old['permanent_cache_retained']);dst=b.parent/'codex-cx-slice-s-compose4-cache-20261029/NEL_final_objects_20261102'
assert src==b.parent/'codex-cx-slice-s-compose3-cache-20261029/NEL_final_objects_20261102'
assert not dst.exists()
expected={Path(x['destination']).name:x for x in old['copied']}
assert {p.name for p in src.iterdir()}==set(expected)
for n,row in expected.items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==row['sha256']
shutil.move(str(src),str(dst))
assert not src.exists()
for row in old['copied']:
 row['destination']=str(dst/Path(row['destination']).name)
 assert hashlib.sha256(Path(row['destination']).read_bytes()).hexdigest()==row['sha256']
old['permanent_cache_retained']=str(dst)
old['archive_path_correction']=dict(accidental_owned_directory=str(src),corrected_owned_directory=str(dst),only_newly_created_NEL_files_moved=True,predecessor_original_files_modified=False)
(b/'NEL_CACHE_FINAL.json').write_text(json.dumps(old,indent=1)+'\n')
print(json.dumps(old['archive_path_correction']))
