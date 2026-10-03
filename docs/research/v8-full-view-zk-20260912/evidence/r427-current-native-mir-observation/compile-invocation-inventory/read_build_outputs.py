#!/usr/bin/env python3
"""Read-only scan of Cargo build-script output records for native link/env directives."""
import hashlib,json,pathlib
root=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/target/release/build')
rows=[]
for p in sorted(root.glob('*/output')):
    text=p.read_text(errors='replace')
    lines=[line for line in text.splitlines() if line.startswith(('cargo:rustc-link-search=','cargo:rustc-link-lib=','cargo:rustc-env=','cargo:rustc-cfg=')) or line.startswith(('rustc-link-search=','rustc-link-lib=','rustc-env=','rustc-cfg='))]
    if lines:
        rows.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'directives':lines})
print(json.dumps({'scan_root':str(root),'output_records_with_relevant_directives':len(rows),'records':rows},indent=2,sort_keys=True))
