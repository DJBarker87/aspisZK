from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029');entries=[]
for r in json.loads((H/'resolution.json').read_text()):entries.append(dict(path=r['path'],sha256=r['sha256'],kind='effective external',module=r['module'],cohort=r['cohort']))
for r in json.loads((H/'fmt-physical-objects.json').read_text()):entries.append(dict(path=r['path'],sha256=r['sha256'],kind='physical Fmt'))
for r in json.loads((H/'claim-object-locations.json').read_text()):
 for x in r['objects']:entries.append(dict(path=x['path'],sha256=x['sha256'],kind='closing object variant',row=r['id']))
if(H/'receipt-recovered-objects.json').exists():
 for r in json.loads((H/'receipt-recovered-objects.json').read_text()):
  if r['selected']:
   x=r['selected'];entries.append(dict(path=x['path'],sha256=x['sha256'],kind='receipt recovered closing object',row=r['id']))
cache={};changes=[]
for r in entries:
 p=r['path']
 if p not in cache:
  f=Path(p)
  if f.is_file():
   h=hashlib.sha256()
   with f.open('rb')as s:
    while b:=s.read(4*1024*1024):h.update(b)
   cache[p]=h.hexdigest()
  else:cache[p]=None
 if cache[p]!=r['sha256']:changes.append(dict(**r,after_sha256=cache[p]))
out=dict(entries=len(entries),distinct_paths=len(cache),changes=changes,source_revision=(H/'revision').read_text().strip(),operation='post-audit read-only integrity check; private build outputs excluded')
(H/'post-integrity.json').write_text(json.dumps(out,indent=1));print(json.dumps(out,indent=1))
# Preserve each exact preflight inventory, compressed without a large intermediate file.
import lzma
h=hashlib.sha256();count=0
with lzma.open(H/'preflight-resolutions.jsonl.xz','wb',preset=6)as z:
 for p in sorted(H.glob('pinned-resolution-pre-*.json')):
  data=p.read_bytes();line=(json.dumps(dict(path=p.name,sha256=hashlib.sha256(data).hexdigest(),original_utf8=data.decode()),separators=(',',':'))+'\n').encode();h.update(line);z.write(line);count+=1
(H/'preflight-resolutions.jsonl.sha256').write_text(h.hexdigest()+'  preflight-resolutions.jsonl\n')
expected_lean='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550';e=json.loads((H/'authority.json').read_text());actual_lean=hashlib.sha256(Path(e['LEAN']).read_bytes()).hexdigest()
summary=dict(preflight_count=count,uncompressed_jsonl_sha256=h.hexdigest(),compressed_sha256=hashlib.sha256((H/'preflight-resolutions.jsonl.xz').read_bytes()).hexdigest(),lean_binary_sha256=actual_lean,matches_NDR_recorded_lean_binary=actual_lean==expected_lean)
(H/'preflight-archive.json').write_text(json.dumps(summary,indent=1));print(json.dumps(summary,indent=1))
