#!/usr/bin/env python3
"""Read-only host source/tool provenance; mismatches never become frozen pins."""
import hashlib,json,subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory-20261021')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected=json.loads((H/'frozen-source-hashes.json').read_text())
source=[]
for f in expected['files']:
 p=H/'src'/f['path']
 source.append(dict(path=f['path'],frozen_sha256=f['sha256'],host_sha256=sha(p) if p.is_file() else None,host_matches_frozen=p.is_file() and sha(p)==f['sha256']))
files=set()
for p in (H/'collected').glob('*.json'):
 x=json.loads(p.read_text())
 for d in x.get('declarations',[]):
  name=d.get('file',{});name=name.get('Local') if isinstance(name,dict) else None
  if name:files.add(name)
external=[]
for name in sorted(files):
 if not name.startswith('/'):continue
 candidates=[Path(name)]
 if name.startswith('/cargo/'):candidates.append(Path.home()/'.cargo'/name[len('/cargo/'):])
 if name.startswith('/rustc/library/'):
  candidates.append(Path.home()/'.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust'/name[len('/rustc/'):])
 p=next((p for p in candidates if p.is_file()),None)
 external.append(dict(reported_path=name,resolved_path=str(p) if p else None,sha256=sha(p) if p else None,bytes=p.stat().st_size if p else None,status='hashed diagnostic dependency source' if p else 'unresolved remapped/toolchain source'))
tools={}
for name,p in [('charon',Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')),('charon-driver',Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon-driver')),('diagnostic-rustc',Path.home()/'.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc')]:
 tools[name]=dict(path=str(p),sha256=sha(p))
result=dict(schema='s10-diagnostic-source-provenance-v1',frozen_source_revision=expected['source_revision'],host_source_comparison=source,external_sources=external,tools=tools,scope='Diagnostic source hashes only. Native nightly/forced cfg is not frozen SBF Rust/LLVM; macro span and inline instance correspondence remain open.')
(H/'collected/source-provenance.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(host_files=len(source),matches=sum(s['host_matches_frozen'] for s in source),external_files=len(external),external_unresolved=sum(s['sha256'] is None for s in external))))
