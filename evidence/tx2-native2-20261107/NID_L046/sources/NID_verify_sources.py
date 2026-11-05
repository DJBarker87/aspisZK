"""Strict owned source audit; frozen payload and shared tools are read-only."""
from pathlib import Path
import hashlib,json,re,lzma,base64
B=Path.cwd();sha=lambda raw:hashlib.sha256(raw).hexdigest()
P=B.parent/'codex-cx-extract-stage-20261106'
manifest=json.loads((P/'NHR_STAGING_MANIFEST.json').read_text());assert manifest['revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
raw=lzma.decompress((P/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes());assert sha(raw)==(P/'NHR_FROZEN_PAYLOAD.json.sha256').read_text().strip()
frozen=json.loads(raw);S=B/'NID_src';pins=json.loads((B/'NID_SOURCE_PINS.json').read_text())
for n,h in pins.items():assert sha((S/n).read_bytes())==h,n
for n,pin in manifest['files'].items():
 original=base64.b64decode(frozen[n],validate=True);assert sha(original)==pin['sha256']
 actual=(S/n).read_bytes()
 if n=='crates/aspis-r1-cost-probe/src/candidate.rs':actual=actual.removesuffix(b'\n#[cfg(kani)] #[path="NID_native.rs"] mod NID_native;\n')
 if n=='crates/aspis-r1-cost-probe/src/lib.rs':
  actual=actual.removesuffix(b'\n#[cfg(kani)] include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n')
  actual=actual.replace(b'\n#![cfg_attr(kani,feature(allocator_api))]',b'')
 assert actual==original,('frozen source erasure mismatch',n)
for m in json.loads((B/'NID_MODULES.json').read_text()):
 s=(B/'NID_generated'/(m+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option max(Heartbeats|RecDepth)',s,re.M),m
native=(S/'crates/aspis-r1-cost-probe/src/NID_native.rs').read_text()
assert not re.search(r'\bstatic\s+(mut\s+)?\w+\s*:|stub_verified|proof_for_contract',native)
assert 'mul(' not in native and '.digest(' in native
out=dict(status='PASS',frozen_files=len(manifest['files']),native_source_sha256=sha(native.encode()),shipped_files_modified=False,cfg_kani_erasure='byte-identical frozen source',module_count=len(json.loads((B/'NID_MODULES.json').read_text())),authored_modules_no_admissions_or_limit_raises=True)
(B/'NID_SOURCE_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
