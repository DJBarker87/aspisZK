from pathlib import Path
import json,lzma,hashlib,shutil
B=Path.cwd();cfg=json.loads((B/'NNM_SEED_CONFIG.json').read_text());rows=[]
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,q,expected=None):
 assert p.is_file(),str(p)
 h=H(p)
 if expected:assert h==expected,(str(p),'pin mismatch')
 q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert H(q)==h,str(q)
 else:shutil.copy2(p,q)
 assert H(q)==h
 rows.append(dict(path=str(p),destination=str(q),sha256=h,bytes=p.stat().st_size))
def object(p,dest,expected=None):
 copy(p,dest,expected)
 for s in ['.private','.server']:
  q=Path(str(p)+s)
  if q.exists():copy(q,Path(str(dest)+s))
 q=p.with_suffix('.ir')
 if q.exists():copy(q,dest.with_suffix('.ir'))
for row in cfg['previous_export']['files']:
 p=Path(row['path']);object(p,B/'NNM_previous'/p.name,row['sha256'])
seen=set()
for root in cfg['tx1_paths']:
 for p in sorted(Path(root).glob('NNG_*.olean')):
  if p.name in seen:continue
  seen.add(p.name);object(p,B/'NNM_tx1'/p.name)
root=Path(cfg['tx1_paths'][1])
for name in cfg['wrapper_modules']:
 p=root/(name+'.olean');object(p,B/'NNM_wrapperR4'/p.name)
for row in cfg['tx2_objects']:
 p=Path(row['path']);object(p,B/'NNM_tx2'/p.name,row['sha256'])
p=Path(cfg['raw_binary']);copy(p,B/'NNM_native/NNM_ProofDriver','46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c')
(B/'NNM_RAW_BINARY.json').write_text(json.dumps(rows[-1],indent=1)+'\n')
raw=json.dumps(dict(files=rows,deletions=0,disk=shutil.disk_usage(B)._asdict()),indent=1).encode()
(B/'NNM_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw));(B/'NNM_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes']for x in rows),disk=shutil.disk_usage(B)._asdict())))
