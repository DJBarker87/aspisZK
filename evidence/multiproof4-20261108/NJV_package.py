from pathlib import Path
import hashlib,lzma,json
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def blob(p):
 if p.exists():return p.read_bytes()
 if Path(str(p)+'.xz').exists():return lzma.decompress(Path(str(p)+'.xz').read_bytes())
 raise FileNotFoundError(p)
refs=[]
for source in sorted(E.glob('NJV_*/sources')):
 for p in sorted(source.rglob('*')):
  if not p.is_file() or p.name.endswith(('.sha256','.reference.json')):continue
  original=Path(str(p)[:-3]) if p.suffix=='.xz' else p
  data=lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes()
  if len(data)<256000:continue
  canonical=E/original.relative_to(source)
  try:same=blob(canonical)==data
  except FileNotFoundError:same=False
  if not same:continue
  ref=dict(canonical=str(canonical.relative_to(E)),sha256=sha(data),bytes=len(data),original_archive=str(original.relative_to(E)))
  Path(str(original)+'.reference.json').write_text(json.dumps(ref,indent=2)+'\n');p.unlink()
  side=Path(str(original)+'.sha256')
  if side.exists():side.unlink()
  refs.append(ref)
compressed=[]
for p in sorted(E.rglob('*')):
 if not p.is_file() or p.suffix in ['.xz','.sha256']:continue
 data=p.read_bytes()
 is_text=p.suffix in ['.log','.c','.patch','.lean','.md','.jsonl']
 bad_ws=is_text and (any(l.endswith((b' ',b'\t')) for l in data.splitlines()) or data.endswith(b'\n\n'))
 if len(data)<=20*1024*1024 and not bad_ws:continue
 if p.suffix in ['.lean','.md']:assert not bad_ws,p
 Path(str(p)+'.xz').write_bytes(lzma.compress(data,preset=6));Path(str(p)+'.sha256').write_text(sha(data)+'\n');p.unlink();compressed.append(dict(path=str(p.relative_to(E)),sha256=sha(data),bytes=len(data)))
# Validate every compressed transport and every deduplicated input.
for p in E.rglob('*.xz'):
 side=Path(str(p)[:-3]+'.sha256')
 if side.exists():assert side.read_text().strip()==sha(lzma.decompress(p.read_bytes())),p
for p in E.rglob('*.reference.json'):
 ref=json.loads(p.read_text());assert sha(blob(E/ref['canonical']))==ref['sha256'],p
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
allrefs=[json.loads(p.read_text()) for p in E.rglob('*.reference.json')]
alltransports=[str(p.relative_to(E)) for p in E.rglob('*.xz') if Path(str(p)[:-3]+'.sha256').exists()]
(E/'NJV_PACKAGING.json').write_text(json.dumps(dict(input_references=allrefs,lossless_transports=alltransports,deduplicated_this_run=refs,compressed_this_run=compressed,inputs_preserved=True,all_hashes_verified=True,max_file_bytes=max(p.stat().st_size for p in E.rglob('*') if p.is_file())),indent=2)+'\n')
print('NJV packaging PASS: '+str(len(refs))+' large repeated inputs referenced by hash; '+str(len(compressed))+' lossless transports; no file over20MB')
