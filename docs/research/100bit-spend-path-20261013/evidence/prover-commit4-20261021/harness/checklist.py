#!/usr/bin/env python3
"""Preserve the exact nine source rows; component checks do not close rows."""
import hashlib,json
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R=next(p for p in E.parents if (p/'Cargo.toml').exists())
p=R/'docs/research/v8-r0-zk-20261009/r1p-final/PRIVACY-FINAL-20261020.md'
rows=[s for s in p.read_text().splitlines() if s.startswith('| R_commit_')]
assert len(rows)==9
packet=dict(checklist_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),rows=[dict(before_verbatim=s,after_verbatim=s,discharged=False) for s in rows])
(E/'checklist-before-after.json').write_text(json.dumps(packet,indent=2)+'\n')
