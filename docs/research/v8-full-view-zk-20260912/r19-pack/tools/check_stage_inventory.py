#!/usr/bin/env python3
"""Fail closed unless the literal staged ORDER equals the generated T163 plan."""
import argparse,ast,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('basis_tables',type=Path);a=p.parse_args()
expected=json.loads((Path(__file__).resolve().parents[1]/'evidence/correction_plan.json').read_text())
m=re.search(r'\bORDER\s*:\s*\[usize\s*;\s*1024\]\s*=\s*(\[[\s\S]*?\])\s*;',a.basis_tables.read_text())
if not m:raise SystemExit('FAIL: no literal 1024-entry usize ORDER; do not guess inventory')
if ast.literal_eval(m[1])!=expected['order']:raise SystemExit('FAIL: staged ORDER differs from generated plan')
print('PASS: every staged ORDER entry matches the generated T163 plan')
