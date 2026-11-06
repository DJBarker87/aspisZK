from pathlib import Path
import json,lzma,base64,hashlib,difflib
B=Path.cwd();S=B/'NJG_src';sha=lambda b:hashlib.sha256(b).hexdigest();pins=json.loads((B/'NJG_SOURCE_PINS.json').read_text());payload=json.loads(lzma.decompress((B/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()));out=[];rows=[]
for n,h in pins.items():
 old=base64.b64decode(payload[n]).decode();new=(S/n).read_text();assert sha(new.encode())==h
 out.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 added=[line[1:] for line in difflib.unified_diff(old.splitlines(),new.splitlines()) if line.startswith('+') and not line.startswith('+++')]
 rows.append(dict(file=n,source_sha256=h,added_lines=len(added),assertions=[line.strip() for line in added if 'assert' in line],deployed_bytes_modified=False))
patch=''.join(out);(B/'NJG_FINAL_NATIVE.patch').write_text(patch)
result=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',patch_sha256=sha(patch.encode()),cut_source_sha256=sha((B/'NJG_generated/NJG_NativeCuts.lean').read_bytes()),kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',files=rows,policy='Scratch-only harness patch; original shipped files remain unchanged; complete source asserted text retained for reviewed (ai)(5) transcription')
(B/'NJG_ASSERTIONS.json').write_text(json.dumps(result,indent=2));print(json.dumps(dict(status='PASS',patched_files=len(rows),patch_bytes=len(patch),patch_sha256=result['patch_sha256'])))
