from pathlib import Path
import json,hashlib,shutil,sys
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJB_20261107/NJB_exports_20261107');C.mkdir(parents=True,exist_ok=True)
for mode in ['fixtures','proof0','proof1','scan']:
 r=json.loads((B/'NJB_audit'/mode/'receipt.json').read_text());assert r['exit_status']==0
 if mode.startswith('proof'):assert r['standard_only']
 if mode=='fixtures':assert r['fixture_pass']
 if mode=='scan':assert not(r['dangling']or r['duplicate_owners']or r['import_mismatch'])
g=json.loads((B/'NJB_GATE_SOURCES.json').read_text());mods=sorted(set(g['passed'])|{'NJB_COMBINED_IMPORT','CopyActiveMaskBasisFacts','CopyActiveMaskBasisRegroup'});rows=[]
for m in mods:
 source=B/'NJB_objects'/(m+'.olean');assert source.is_file(),m
 for p in [source,Path(str(source)+'.private'),Path(str(source)+'.server'),source.with_suffix('.ir')]:
  if not p.exists():continue
  q=C/p.name;h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,'Never replace a changed retained export'
  else:shutil.copy2(p,q)
  rows.append(dict(module=m,source=str(p),path=str(q),sha256=h,bytes=q.stat().st_size))
out=dict(cache=str(C),files=rows,bytes=sum(x['bytes']for x in rows),modules=mods,paths=[str(C)]+json.loads((B/'NJB_PATHS.json').read_text()),base='coherent SInt2 via NIU retained export',delete_cache=False,pin_actual_runtime_libraries='see L090/L091/L092/L093/L096 deps_fingerprint.selected_objects',candidate='TX1:268 only; all other new packets SUPPORT; next ledger gate required')
(B/'NJB_EXPORT.json').write_text(json.dumps(out,indent=1));print(json.dumps(dict(modules=len(mods),bytes=out['bytes'],cache=str(C))))
