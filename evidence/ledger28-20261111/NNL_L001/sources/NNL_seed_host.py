from pathlib import Path
import json,lzma,hashlib,shutil
B=Path.cwd();cfg=json.loads((B/'NNL_SEED_CONFIG.json').read_text());H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=[]
def copy(src,dst,expected=None):
 assert src.is_file(),str(src)
 h=H(src)
 if expected:assert h==expected,(str(src),'pin mismatch')
 dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert H(dst)==h
 else:shutil.copy2(src,dst)
 assert H(dst)==h
 rows.append(dict(path=str(src),destination=str(dst),sha256=h,bytes=src.stat().st_size))
for source,tag in zip(cfg['candidate_paths'],['NNL_candidateR4','NNL_candidateF9','NNL_candidateRSL3','NNL_candidateOwn']):
 root=Path(source)
 for p in root.rglob('*'):
  if p.is_file()and any(str(p).endswith(s)for s in['.olean','.olean.private','.olean.server','.ir']):copy(p,B/tag/p.relative_to(root))
root=Path(cfg['library_export'])
for p in root.rglob('*'):
 if p.is_file():copy(p,B/'NNL_libraryF9'/p.relative_to(root))
x=cfg['previous'];root=Path(x['export'])
for row in x['files']:
 p=Path(row['path']);copy(p,B/'NNL_previous'/p.relative_to(root),row['sha256'])
raw=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNK_20261111/NNK_native/NNK_ProofDriver')
copy(raw,B/'NNL_native/NNL_ProofDriver','46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c')
(B/'NNL_RAW_BINARY.json').write_text(json.dumps(rows[-1],indent=1)+'\n')
pins=[]
# Retain the exact host input source associated with the selected candidate objects.
for directory in ['NNG_generated','NNG_rev4_inputs']:
 root=Path('/home/dombarker/project-offloads/codex-cx-tx1-principal-20261111')/directory
 for p in root.rglob('*.lean'):
  q=B/'NNL_supplier_sources'/directory/p.relative_to(root)
  copy(p,q);pins.append(dict(path=str(p),destination=str(q),sha256=H(p)))
(B/'NNL_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
raw=json.dumps(dict(files=rows,source_pins=pins,cache_retained=True,deletions=0,disk=shutil.disk_usage(B)._asdict()),indent=1).encode();(B/'NNL_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(B/'NNL_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(files=len(rows),source_files=len(pins),bytes=sum(r['bytes']for r in rows),disk=shutil.disk_usage(B)._asdict())))
