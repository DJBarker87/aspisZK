"""Strict owned source audit; frozen payload and shared tools are read-only."""
from pathlib import Path
import hashlib,json,re,lzma,base64
B=Path.cwd();sha=lambda raw:hashlib.sha256(raw).hexdigest()
P=B.parent/'codex-cx-extract-stage-20261106'
manifest=json.loads((P/'NHR_STAGING_MANIFEST.json').read_text());assert manifest['revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
raw=lzma.decompress((P/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes());assert sha(raw)==(P/'NHR_FROZEN_PAYLOAD.json.sha256').read_text().strip()
frozen=json.loads(raw);S=B/'NIL_src';pins=json.loads((B/'NIL_SOURCE_PINS.json').read_text())
for n,h in pins.items():assert sha((S/n).read_bytes())==h,n
for n,pin in manifest['files'].items():
 original=base64.b64decode(frozen[n],validate=True);assert sha(original)==pin['sha256']
 actual=(S/n).read_bytes()
 if n in ['crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/verifier.rs']:
  assert actual.startswith(original),('frozen body modified',n)
  suffix=actual[len(original):]
  allowed={'candidate.rs':['tree','key','parent'],'verifier.rs':['reader','ctor','resume_prefix','header']}[Path(n).name]
  for module in allowed:
   block=('#[cfg(kani)]\n#[path="NIL_'+module+'_native.rs"]\nmod NIL_'+module+'_native;').encode()
   assert suffix.count(block)<=1,('duplicate module',n,module)
   suffix=suffix.replace(block,b'')
  assert suffix.strip()==b'',('unapproved addition',n)
  actual=original
 if n=='crates/aspis-r1-cost-probe/src/lib.rs':
  actual=actual.removesuffix(b'\n#[cfg(kani)] include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n')
  actual=actual.replace(b'\n#![cfg_attr(kani,feature(allocator_api))]',b'')
 assert actual==original,('frozen source erasure mismatch',n)
for row in json.loads((B/'NIL_MODULES.json').read_text())['selected']:
 m=row['module']
 s=(B/'NIL_generated'/(m+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option max(Heartbeats|RecDepth)',s,re.M),m
natives=list((S/'crates/aspis-r1-cost-probe/src').glob('NIL_*_native.rs'))
for p in natives:
 native=p.read_text()
 assert not re.search(r'\bstatic\s+(mut\s+)?\w+\s*:|stub_verified|proof_for_contract',native),p
 assert '.mul(' not in native,p
out=dict(status='PASS',frozen_files=len(manifest['files']),native_sources={str(p.relative_to(S)):sha(p.read_bytes()) for p in natives},shipped_files_modified=False,cfg_kani_erasure='byte-identical frozen source',module_count=len(json.loads((B/'NIL_MODULES.json').read_text())['selected']),authored_modules_no_admissions_or_limit_raises=True)
(B/'NIL_SOURCE_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
