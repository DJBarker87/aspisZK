#!/usr/bin/env python3
"""Host-only: replace owned constructor's validator with control-flow reference."""
import pathlib,json,hashlib,sys,subprocess
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref9-20261021')
p=R/'source/tools/r1-builder-reference/tree.rs'
a=p.read_text();old='inner.validate_with_empty_roots(&empty)?;';new='validate_owned(inner, empty)?;'
assert a.count(old)==1
p.write_text(a.replace(old,new))
(R/'validator-substitution.json').write_text(json.dumps(dict(before_sha256=hashlib.sha256(a.encode()).hexdigest(),after_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),old=old,new=new,status='Exploratory P6 reference substitution; no semantic admission certificate'),indent=2)+'\n')
sys.exit(subprocess.run(['python3',str(R/'extract.py'),sys.argv[1],'drop-opaque-validator']).returncode)
