#!/usr/bin/env python3
"""Run on the host: compact diagnostics beside immutable receipts."""
import hashlib,json,re,subprocess
from pathlib import Path
BASE=Path('/home/dombarker/project-offloads/codex-cx-r22-overflow2-20261021')
for path in sorted((BASE/'receipts').glob('*/receipt.json')):
    rec=json.loads(path.read_text())
    so=(path.parent/'stdout.log').read_text();se=(path.parent/'stderr.log').read_text()
    diagnostic=dict(stdout_sha256=hashlib.sha256(so.encode()).hexdigest(),stderr_sha256=hashlib.sha256(se.encode()).hexdigest(),verification_summary=so.splitlines()[-3:])
    if rec['exit_status']:
        match=re.search(r'^error(?:\[|:)',so,re.M)
        diagnostic.update(stderr=se,compiler_errors=so[match.start():] if match else '',failed_properties=[s for s in so.splitlines() if 'FAILURE' in s])
    dest=path.parent/'diagnostics.json'
    if dest.exists():assert json.loads(dest.read_text())==diagnostic
    else:dest.write_text(json.dumps(diagnostic,indent=2)+'\n')
solver=BASE/'solver/bin/z3'
if solver.exists():
    d=dict(z3_path=str(solver),sha256=hashlib.sha256(solver.read_bytes()).hexdigest(),size_bytes=solver.stat().st_size,version=subprocess.check_output([str(solver),'--version'],text=True).strip(),provenance='Read-only copy of already installed host executable; no solver build or committed binary')
    (BASE/'solver-environment.json').write_text(json.dumps(d,indent=2)+'\n')
