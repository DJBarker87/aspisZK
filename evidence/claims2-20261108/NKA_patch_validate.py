from pathlib import Path
import json,lzma,base64,hashlib,difflib
B=Path.cwd();S=B/'NKA_src'
payload=json.loads(lzma.decompress((B/'NKA_FROZEN_PAYLOAD.json.xz').read_bytes()))
pins=json.loads((B/'NKA_SOURCE_PINS.json').read_text());patch='';rows=[]
for name,h in sorted(pins.items()):
 p=S/name;assert hashlib.sha256(p.read_bytes()).hexdigest()==h,name
 if name not in payload:continue
 old=base64.b64decode(payload[name]).decode();new=p.read_text()
 diff=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name,tofile='b/'+name));patch+=diff
 assert not any(l.startswith('-') and not l.startswith('---') for l in diff.splitlines()),name
 inserts=[]
 for tag,i,j,k,l in difflib.SequenceMatcher(None,old.splitlines(True),new.splitlines(True),autojunk=False).get_opcodes():
  if tag=='equal':continue
  assert tag=='insert',(name,tag)
  block=''.join(new.splitlines(True)[k:l]).strip()
  assert block.startswith('#[cfg(kani)]') or block.startswith('#![cfg_attr(kani,'),(name,block[:200])
  inserts.append(dict(first_line=block.splitlines()[0],lines=l-k))
 rows.append(dict(path=name,original_body_unchanged=True,cfg_kani_insertions=inserts))
assert patch==(B/'NKA_NATIVE.patch').read_text(),'stale patch'
assert len(rows)==5
result=dict(status='PASS',original_frozen_source_preserved=True,rows=rows,patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),kmx_patch_sha256=hashlib.sha256((B/'NKA_KMX.patch').read_bytes()).hexdigest(),cargo_target_dir=str(B/'NKA_target'))
(B/'NKA_PATCH_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print('NKA exact native patch and frozen source-body preservation PASS')
