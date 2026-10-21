#!/usr/bin/env python3
"""Validate inherited source pins with this continuation's assigned base."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s7-kani3-20261021'
old=json.loads((B/'evidence/s7-kani-20261021/source-binding.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for path,pin in old['source_files'].items():assert sha(R/path)==pin,path
for path,pin in old['generated'].items():assert sha(R/'tools/s7-kani-20261021'/path)==pin,path
for path,pin in old['reference_sources'].items():assert sha(R/'tools/s7-kani-20261021'/path)==pin,path
changed=subprocess.check_output(['git','diff','--name-only','da6f0085a','--','crates','programs'],cwd=R,text=True).splitlines()
assert not changed,changed
inherited=subprocess.check_output(['git','diff','--name-only','072b24afc','da6f0085a','--','crates','programs'],cwd=R,text=True).splitlines()
(E/'source-preflight.json').write_text(json.dumps(dict(base='da6f0085a',old_base='072b24afc',source_pins=old['source_files'],generated=old['generated'],reference_sources=old['reference_sources'],this_continuation_shipped_changes=changed,inherited_shipped_changes=inherited,old_generator_check='Failed only at old-base aggregate shipped_changes assertion; source/generated/reference hash checks pass under this base-aware preflight',status='PASS'),indent=2)+'\n')
print('Assigned-base shipped diff empty; all inherited frozen source/reference/generated pins pass')
