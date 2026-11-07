"""Run only in the own host scope: immutable exports, raw evidence, all input hashes."""
from pathlib import Path
import json,hashlib,lzma,shutil,tarfile
B=Path.cwd();C=B.parent/'codex-pc-deposit-children2-cache-20261110'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
pins=json.loads(lzma.decompress((B/'PCI_IMPORTS.json.xz').read_bytes()))
assert all(sha(C/n)==v['sha256'] for n,v in pins.items())
plan=json.loads((B/'PCI_AUDIT_ROOTS_ALL.json').read_text())
mods=plan['module_closure']+['PCI_COMBINED_IMPORT']
mods+=['PCC_Reference','PCC_DepositDecodeReference','PCC_PairValidation','PCC_SingleOutputReference','PCC_LaneReference']
files=[]
for m in mods:
 stem=m.replace('.','/')
 for p in sorted(set((B/'PCI_objects'/stem).parent.glob(Path(stem).name+'.olean*')) | {B/'PCI_objects'/(stem+ext) for ext in ['.ir','.ilean'] if (B/'PCI_objects'/(stem+ext)).is_file()}):
  if not p.is_file():continue
  files.append(dict(module=m,module_file=str(p.relative_to(B/'PCI_objects')),source=str(p),sha256=sha(p),bytes=p.stat().st_size,classification='unchanged privately compiled dependency' if m.startswith('PCC_') else 'PCI accepted import support'))
key=hashlib.sha256(json.dumps(files,sort_keys=True).encode()).hexdigest()[:12];D=C/('PCI_exports_20261110_'+key);D.mkdir(exist_ok=True)
for r in files:
 p=Path(r['source']);q=D/r['module_file'];q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==r['sha256']
 else:shutil.copyfile(p,q)
 assert sha(q)==r['sha256'];r['export_path']=str(q)
raw=[];R=B/'PCI_RAW_FINAL';R.mkdir(exist_ok=True)
for p in sorted(B.glob('PCI_NEP_*')):
 if not p.is_file():continue
 q=R/(p.name+'.xz')
 with p.open('rb') as f,lzma.open(q,'wb') as g:
  for chunk in iter(lambda:f.read(1048576),b''):g.write(chunk)
 (R/(p.name+'.sha256')).write_text(sha(p)+'\n')
 raw.append(dict(source=p.name,uncompressed_sha256=sha(p),uncompressed_bytes=p.stat().st_size,compressed_sha256=sha(q),compressed_bytes=q.stat().st_size))
binary={str(p.relative_to(B)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in [B/'PCI_native/PCI_AuditDriver',B/'PCI_native/PCI_AuditDriver.c',B/'PCI_native/PCI_WALKER.c',B/'PCI_native/PCI_MemoryLimit.c']}
(B/'PCI_AUDIT_BINARY_PINS.json').write_text(json.dumps(binary,indent=1)+'\n')
(B/'PCI_RAW_MANIFEST.json').write_text(json.dumps(dict(files=raw,binary=binary,all_import_pins_unchanged=True,import_files=len(pins)),indent=1)+'\n')
export=dict(export_directory=str(D),files=files,lean_path=[str(D),str(C)],seed_manifest_sha256=sha(B/'PCI_IMPORTS.json.xz'),copy_only=True,hardlinks=False,deletions=0,cache_retained=True,all_export_hashes_verified=True,host_free_bytes=shutil.disk_usage(B).free)
(B/'PCI_EXPORT.json').write_text(json.dumps(export,indent=1)+'\n');(D/'PCI_EXPORT.json').write_text(json.dumps(export,indent=1)+'\n')
print(json.dumps(dict(exports=len(files),raw_files=len(raw),all_import_pins_unchanged=True,export_directory=str(D),host_free_bytes=shutil.disk_usage(B).free)))

with tarfile.open(B/'PCI_RAW_BUNDLE.tar.xz','w:xz') as t:
 for p in sorted(R.iterdir()):t.add(p,arcname='PCI_RAW_FINAL/'+p.name)
(B/'PCI_RAW_BUNDLE.tar.xz.sha256').write_text(sha(B/'PCI_RAW_BUNDLE.tar.xz')+'  PCI_RAW_BUNDLE.tar.xz\n')
