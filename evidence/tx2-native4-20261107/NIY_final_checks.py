"""Own final source/cache/tool pinning and export; no shared infrastructure mutation."""
from pathlib import Path
import os,json,hashlib,shutil,subprocess,lzma
B=Path.cwd();C=B.parent/'codex-cx-slice-d-prepared-cache-20261104';T=Path(os.environ['LEAN_SYSROOT'])
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
mods=json.loads((B/'NIY_MODULES.json').read_text())['selected'];source_checks=[]
for row in mods:
 n=row['module'];p=B/'NIY_generated'/(n+'.lean');r=json.loads((B/row['receipt']).read_text());expected=row['source_sha256']
 assert sha(p)==expected and r['exit_status']==0 and r['source_hashes']['NIY_generated/'+n+'.lean']==expected,n
 source_checks.append(dict(module=n,source_sha256=expected,receipt=row['receipt']))
seed=json.loads((B/'NIY_SEED.json').read_text());seed=seed.get('seed',[]) if isinstance(seed,dict) else seed
for r in seed:
 assert sha(Path(r['destination']))==r['sha256'] and sha(Path(r['source']))==r['sha256'],r
pins=json.loads((B/'NIY_SOURCE_PINS.json').read_text())
for n,h in pins.items():assert sha(B/'NIY_src'/n)==h,('scratch source mismatch',n)
assert sha(B/'NIY_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(B/'NIY_SOURCE_VERIFICATION.json').write_text(json.dumps(dict(status='PASS',selected=source_checks,seed_files=len(seed),seed_bytes=sum(r['bytes'] for r in seed),scratch_files=len(pins)),indent=2)+'\n')
# Same pinned tool inspection as the retained NIL script, inside this admitted scope.
paths=[B/'S2W_run_host.py',B/'S2W_lean_host.py',T/'bin/lean',T/'bin/lake',T/'bin/leanc',Path('/home/dombarker/.cargo/bin/cargo-kani')]
for root in [Path('/home/dombarker/.kani/kani-0.67.0/bin'),Path('/home/dombarker/.kani/kani-0.67.0/toolchain/bin')]:
 if root.exists():paths += [p for p in root.iterdir() if p.is_file()]
toolpins={str(p):dict(sha256=sha(p),bytes=p.stat().st_size,resolved=str(p.resolve())) for p in paths if p.is_file()};versions={}
for command in [['/home/dombarker/.cargo/bin/cargo-kani','--version'],[str(T/'bin/lean'),'--version']]:
 r=subprocess.run(command,capture_output=True,text=True);assert r.returncode==0;versions[' '.join(command)]=r.stdout+r.stderr
(B/'NIY_TOOL_PINS.json').write_text(json.dumps(dict(pins=toolpins,versions=versions),indent=2)+'\n')
export=C/'NIY_exports_20261107';export.mkdir(exist_ok=True);records=[]
for n in [r['module'] for r in mods]+['NIY_COMBINED_IMPORT']:
 p=B/'NIY_objects'/(n+'.olean');assert p.is_file(),n
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  q=export/z.name;shutil.copyfile(z,q);assert sha(q)==sha(z)
  records.append(dict(source=str(z),destination=str(q),sha256=sha(q),bytes=q.stat().st_size))
roots=[B/'.lake/build/lib/lean',T/'lib/lean']+[Path(x) for x in os.environ['LEAN_PATH'].split(':')]
modules=[json.loads(l)['module'] for l in (B/'NIY_LOADED_scan.jsonl').read_text().splitlines()];selected=[]
for n in modules:
 rel=Path(*n.split('.')).with_suffix('.olean');p=next((r/rel for r in roots if (r/rel).is_file()),None);assert p is not None,n
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():selected.append(dict(module=n,path=str(z),sha256=sha(z),bytes=z.stat().st_size))
raw=json.dumps(dict(modules=len(modules),files=selected),separators=(',',':')).encode();(B/'NIY_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NIY_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(B/'NIY_EXPORT.json').write_text(json.dumps(dict(own_exports=records,export_bytes=sum(r['bytes'] for r in records),closure_modules=len(modules),closure_files=len(selected),closure_raw_bytes=len(raw),closure_sha256=hashlib.sha256(raw).hexdigest()),indent=2)+'\n')
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
  if str(cwd).startswith(str(B)) and any(z in cmd for z in ['/bin/lean','cargo-kani','cbmc','charon','aeneas']):active.append(dict(pid=int(p.name),command=cmd))
 except (OSError,PermissionError):pass
assert not active,active
sizes=[]
for p in [B/'NIY_target',B/'NIY_objects',B/'NIY_tmp',C/'NIY_seed_20261107',export]:
 if p.exists():sizes.append(dict(path=str(p),bytes=int(subprocess.check_output(['du','-sb','--',str(p)],text=True).split()[0])))
(B/'NIY_RETENTION.json').write_text(json.dumps(dict(status='PASS',active_own_formal_processes=active,retained=sizes,removed=[],all_own_caches_retained=True,disk_free_bytes=shutil.disk_usage(B).free,verified_export_files=len(records),no_key_or_chain_operations=True),indent=2)+'\n')
print(json.dumps(dict(status='PASS',selected_modules=len(mods),seed_bytes=sum(r['bytes'] for r in seed),exports=len(records),closure_modules=len(modules),closure_files=len(selected),active=active)))
