"""Read-only dependency rehash plus own-only export; no deletions."""
from pathlib import Path
import hashlib,json,lzma,shutil,subprocess
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=json.loads((B/'NMV_EXPORT_MODULES.json').read_text())
configs=[]
for p in B.glob('NMV_*.json'):
 try:x=json.loads(p.read_text())
 except (json.JSONDecodeError,UnicodeDecodeError):continue
 if isinstance(x,dict) and 'deps_fingerprint' in x and (B/x['attempt']/'receipt.json').exists():configs.append(x)
pins={};versions={}
for x in configs:
 for path,row in x['deps_fingerprint']['selected_objects'].items():
  versions.setdefault(path,set()).add(row['sha256']);pins[path]=row
changed=[]
for path,row in pins.items():
 p=Path(path);actual=sha(p)
 if not str(p).startswith(str(B)+'/'):
  assert len(versions[path])==1,('Changed inherited dependency during run',path)
  assert actual==row['sha256'],('Changed inherited dependency after run',path)
 elif actual not in versions[path]:changed.append(path)
assert not changed,changed
seed=json.loads((B/'NMV_RETAINED_SEEDS.json').read_text())
for r in seed:
 assert sha(Path(r['destination']))==r['sha256'],r
runner=B/'S2W_run_host.py';inherited=B.parent/'codex-cx-sound-int2-20261025/S2W_run_host.py'
assert sha(runner)==sha(inherited),'Own launcher copy differs from inherited launcher'
support=sorted({x['module'] for x in configs if x['kind']=='support'})
export=B/'NMV_exports_20261111';export.mkdir(exist_ok=True)
rows=[]
for m in sorted(set(modules+support)):
 src=B/'NMV_generated'/(m+'.lean');assert src.is_file(),str(src)
 sources=[src]
 obj=B/'NMV_objects'/(m+'.olean');assert obj.is_file(),str(obj)
 sources += [p for p in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')] if p.is_file()]
 for p in sources:
  dst=export/p.name;shutil.copy2(p,dst)
  assert sha(dst)==sha(p)
  rows.append(dict(source=str(p),path=str(dst),sha256=sha(dst),bytes=dst.stat().st_size))
report=dict(export=str(export),files=rows,proof_modules=modules,unchanged_support_modules=support,no_row_credit=True)
(B/'NMV_EXPORT.json').write_text(json.dumps(report,indent=1)+'\n')
serialized=json.dumps(dict(selected_objects=pins,versions={k:sorted(v) for k,v in versions.items()},seed=seed),sort_keys=True).encode()
(B/'NMV_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(serialized));(B/'NMV_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(serialized).hexdigest()+'\n')
env=json.loads((B/'NMV_ENV.json').read_text());tool=Path(env['LEAN_SYSROOT'])/'bin/lean'
(B/'NMV_TOOL_PINS.json').write_text(json.dumps(dict(lean=str(tool),sha256=sha(tool),version=subprocess.check_output([str(tool),'--version'],text=True).strip()),indent=1)+'\n')
ret=dict(launcher_sha256=sha(runner),selected_objects_rehashed=len(pins),inherited_paths_with_multiple_versions=[p for p,v in versions.items() if len(v)>1 and not p.startswith(str(B)+'/')],seed_files_rehashed=len(seed),own_export_files=len(rows),workspace_bytes=int(subprocess.check_output(['du','-sb',str(B)],text=True).split()[0]),host_free_bytes=shutil.disk_usage(B).free,deletions=0,workspace_retained=str(B),own_objects_retained=str(B/'NMV_objects'),target_retained=str(B/'NMV_target'),tmp_retained=str(B/'NMV_tmp'))
assert ret['host_free_bytes']>=40_000_000_000
(B/'NMV_RETENTION.json').write_text(json.dumps(ret,indent=1)+'\n');print(json.dumps(ret),flush=True)
