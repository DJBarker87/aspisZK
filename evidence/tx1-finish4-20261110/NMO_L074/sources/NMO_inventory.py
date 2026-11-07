"""Final low-memory inventory, scoped, retaining caches and exact import caveat."""
from pathlib import Path
import hashlib,json,lzma,os,shutil,subprocess,time
B=Path.cwd();P=Path('/home/dombarker/project-offloads/codex-cx-tx1-finish3-20261110')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  while chunk:=f.read(1024*1024):h.update(chunk)
 return h.hexdigest()
def inventory(root):
 rows=[];links=[]
 for parent,dirs,files in os.walk(root,followlinks=False):
  for name in dirs+files:
   p=Path(parent)/name
   if p.is_symlink():links.append(dict(path=str(p.relative_to(root)),target=os.readlink(p),resolved=str(p.resolve())))
  for name in files:
   p=Path(parent)/name
   if p.is_file()and not p.is_symlink():rows.append(dict(path=str(p.relative_to(root)),bytes=p.stat().st_size,sha256=sha(p)))
 return dict(root=str(root),files=sorted(rows,key=lambda x:x['path']),links=links,bytes=sum(x['bytes']for x in rows))
source=inventory(P/'NMC_target');own=inventory(B/'NMO_target')
a={x['path']:x for x in source['files']};b={x['path']:x for x in own['files']};same=[k for k in a if k in b and a[k]['sha256']==b[k]['sha256']]
raw=json.dumps(dict(source_cache=source,own_cache=own,matching_import_files=len(same),missing_or_rebuilt_source_paths=len(a)-len(same),timing='RETROSPECTIVE_AFTER_NATIVE_CAMPAIGN',caveat='Initial target copy had no immediate per-file manifest; this inventory does not claim copy-time attestation.',cache_retained=True),indent=1).encode();(B/'NMO_RUST_CACHE_INVENTORY.json.xz').write_bytes(lzma.compress(raw));(B/'NMO_RUST_CACHE_INVENTORY.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
versions={};tools=[]
for name,args in [('cargo-kani',['--version']),('rustc',['--version']),('cargo',['--version'])]:
 exe=shutil.which(name);assert exe,name;r=subprocess.run([exe,*args],capture_output=True,text=True);assert r.returncode==0,(name,r.stderr);versions[name]=r.stdout.strip();p=Path(exe);tools.append(dict(path=str(p),resolved=str(p.resolve()),sha256=sha(p),bytes=p.stat().st_size))
assert '0.67.0'in versions['cargo-kani'],versions
driver=Path(shutil.which('cargo-kani')).resolve()
for name in ['kani-compiler','cbmc','goto-instrument','goto-cc']:
 p=driver.parent/name
 if p.is_file():tools.append(dict(path=str(p),resolved=str(p.resolve()),sha256=sha(p),bytes=p.stat().st_size,role='KANI_DISTRIBUTION_TOOL'))
pins={**json.loads((B/'NMO_FROZEN_FILE_PINS.json').read_text()),**json.loads((B/'NMO_SOURCE_PINS.json').read_text())};wrong=[n for n,h in pins.items()if sha(B/'NMO_src'/n)!=h];assert not wrong,wrong
size=sum(p.lstat().st_size for root,dirs,files in os.walk(B,followlinks=False)for p in[Path(root)/n for n in files]);assert size<30_000_000_000
free=shutil.disk_usage(B).free;assert free>=40_000_000_000
out=dict(status='PASS_FINAL_INVENTORY',source_files_verified=len(pins),rust_cache_import_matching_files=len(same),rust_cache_import_note='Retrospective only; see full manifest/caveat',versions=versions,version_note='rustc/cargo are ambient version queries; actual Kani distribution tools are hashed separately when present',tools=tools,own_bytes=size,free_bytes=free,own_cache_retained=True,TMPDIR_retained=True,symlink_review=own['links'])
(B/'NMO_FINAL_HOST.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in['status','source_files_verified','own_bytes','free_bytes']}))
