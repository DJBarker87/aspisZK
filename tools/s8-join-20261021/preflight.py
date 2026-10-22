#!/usr/bin/env python3
"""Check immutable S8 owners and changed new modules, without old blanket gates."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s8-join-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen=json.loads((B/'evidence/s8-kani-20261021/source-binding.json').read_text())
for path,digest in frozen['source_files'].items():assert sha(R/path)==digest,path
for path,digest in frozen['reference_sources'].items():assert sha(R/'tools/s8-kani-20261021'/path)==digest,path
sources={str(p.relative_to(R)):sha(p) for p in sorted((B/'lean').glob('S8Join*.lean'))}
for name in sources:
 text=(R/name).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',text,re.M),name
changed=subprocess.check_output(['git','diff','--name-only','6c520f134','--','crates','programs'],cwd=R,text=True).splitlines();assert not changed,changed
report=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),frozen_source_files=frozen['source_files'],reference_sources=frozen['reference_sources'],new_sources=sources,shipped_changes=changed,scope='Frozen S8 source/reference hashes and new source scan; not a release manifest replay')
(E/'preflight.json').write_text(json.dumps(report,indent=2)+'\n');print('S8 frozen owner/reference pins match; new modules scan clean; no shipped changes')
