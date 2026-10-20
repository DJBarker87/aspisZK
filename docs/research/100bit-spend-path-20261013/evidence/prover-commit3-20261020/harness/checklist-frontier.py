#!/usr/bin/env python3
"""Preserve verbatim before/after rows; no discharge without a source proof."""
from pathlib import Path
import hashlib,json,subprocess
p=Path('docs/research/v8-r0-zk-20261009/r1p-final/PRIVACY-FINAL-20261020.md')
s=p.read_text()
rows=[line for line in s.splitlines() if line.startswith('| R_commit_')]
assert len(rows)==9,len(rows)
obj={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'checklist_path':str(p),'checklist_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'stage_2':'blocked by Stage 1; no exact quantified source interface discharged','new_lean_module':None,'new_theorems':[],'print_axioms':'N/A: no new Lean declaration','rows':[{'before_verbatim':row,'after_verbatim':row,'discharged':False,'reason':'No verified model of the actual SHA256 byte callback or complete source instance was established.'} for row in rows]}
print(json.dumps(obj,indent=2))
