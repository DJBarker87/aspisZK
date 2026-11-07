from pathlib import Path
import json,base64,lzma,difflib,hashlib
B=Path.cwd();S=B/'NNJ_src';p=S/'programs/r1-cost-probe/src/NNJ_assignment.rs'
old=p.read_text();new=(B/'NNJ_assignment.rs').read_text()
# Only caller j selection changes; exact annotated callee bytes retained.
marker='// Same contract and actual assignment;'
assert old[:old.index(marker)]==new[:new.index(marker)]
assert old[old.index(marker):].count('let window=[0u8;32];let j:usize=kani::any();kani::assume(j<8);')==2
p.write_text(new)
payload=json.loads(lzma.decompress((B/'NNJ_FROZEN_PAYLOAD.json.xz').read_bytes()));extra=json.loads((B/'NNJ_217_KANI_EXTRA_INPUTS.json').read_text())
diffs=[]
for p in sorted(S.rglob('*')):
 if not p.is_file():continue
 rel=str(p.relative_to(S));old=base64.b64decode(payload[rel]) if rel in payload else extra['files'].get(rel,{}).get('text','').encode()
 if old==p.read_bytes():continue
 diffs.extend(difflib.unified_diff(old.decode().splitlines(True),p.read_text().splitlines(True),fromfile='a/'+rel if old else '/dev/null',tofile='b/'+rel))
(B/'NNJ_HARNESSES.patch').write_text(''.join(diffs))
x=json.loads((B/'NNJ_SEED.json').read_text());x['source_files']['programs/r1-cost-probe/src/NNJ_assignment.rs']=hashlib.sha256(new.encode()).hexdigest();x['revision']='fixed-index caller subset after retired K009'
(B/'NNJ_SEED.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps({'native_assignment_callee_body_identical':True,'only_caller_index_split':True,'new_patch_sha256':hashlib.sha256((B/'NNJ_HARNESSES.patch').read_bytes()).hexdigest()}))
