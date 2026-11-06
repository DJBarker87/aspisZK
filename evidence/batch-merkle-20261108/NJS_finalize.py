from pathlib import Path
import json,hashlib,base64,lzma,shutil
import NJS_NHR_stage as stage
B=Path.cwd();S=B/'NJS_workspace';payload=json.loads(lzma.decompress((B/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()))
append=b'\n#[cfg(kani)] mod NJS_native { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../NJS_harness.rs")); }\n'
for name in ['crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/lib.rs']:
 p=S/name;raw=base64.b64decode(payload[name]);patched=raw+append if name.endswith('candidate.rs') else raw.replace(b'#![no_std]',b'#![cfg_attr(kani, feature(allocator_api))]\n#![no_std]',1)
 assert p.read_bytes() in (raw,patched),'unknown owned scratch drift';p.write_bytes(raw)
(B/'NJS_final_preflight').mkdir(exist_ok=True)
manifest=stage.validate(S,B/'NJS_final_preflight','/home/dombarker/.cargo/bin/cargo')
export=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJS_exports_20261108');export.mkdir(exist_ok=True)
pins=[]
for p in sorted((B/'NJS_objects').rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(B/'NJS_objects');dst=export/rel;dst.parent.mkdir(parents=True,exist_ok=True)
 data=p.read_bytes()
 if dst.exists():assert dst.read_bytes()==data
 else:shutil.copy2(p,dst)
 pins.append(dict(path=str(dst),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
(B/'NJS_EXPORT.json').write_text(json.dumps(dict(export=str(export),bytes=sum(x['bytes'] for x in pins),files=pins,source_revision=__import__('os').environ.get('NJS_SOURCE_REVISION')),indent=2)+'\n')
# Only own explicitly named rebuildable cargo output; retain all cache/source/evidence/object/export paths.
target=B/'NJS_target';before=sum(p.stat().st_size for p in target.rglob('*') if p.is_file())
shutil.rmtree(target)
(B/'NJS_CLEANUP.json').write_text(json.dumps(dict(removed=str(target),bytes=before,retained_objects=str(B/'NJS_objects'),retained_export=str(export),keys_touched=False))+'\n')
print('final frozen graph valid; own objects exported and only own Cargo output removed')
