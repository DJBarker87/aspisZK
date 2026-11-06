from pathlib import Path
import json,hashlib,shutil,sys
B=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
export=json.loads((B/'NJZ_EXPORT.json').read_text());seed=json.loads((B/'NJZ_SEED.json').read_text())
for r in export['files']:assert sha(Path(r['retained']))==r['sha256'],r
for r in seed:assert sha(Path(r['destination']))==r['sha256'],r
records=[]
for name in ['NJZ_target','NJZ_tmp']:
 p=B/name;assert p.parent==B and name.startswith('NJZ_')
 size=sum(x.stat().st_size for x in p.rglob('*') if x.is_file() and not x.is_symlink()) if p.exists() else 0
 if p.exists():shutil.rmtree(p)
 records.append(dict(path=str(p),removed_bytes=size,kind='owned rebuildable Cargo target or owned solver temp'))
(B/'NJZ_CLEANUP.json').write_text(json.dumps(dict(status='PASS',verified_exports=len(export['files']),verified_seed_files=len(seed),removed=records,cache_preserved=True,sources_and_receipts_preserved=True,keys_or_wallets_touched=False,free_bytes=shutil.disk_usage(B).free),indent=2)+'\n')
print(json.dumps(dict(status='PASS',freed_bytes=sum(r['removed_bytes'] for r in records),free_bytes=shutil.disk_usage(B).free,cache_preserved=True)))
