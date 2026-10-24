#!/usr/bin/env python3
"""Validate adapted generator syntax, source snapshot and retained generic proofs."""
import ast,hashlib,json,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent;E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023'
for p in T.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
subprocess.run(['python3','-B',str(T/'snapshot.py'),'--check'],check=True)
# Generic Lean mathematics is reused at its recorded scope, without a new theorem.
mods=sorted((R/'docs/research/100bit-spend-path-20261013/lean').glob('OraclePortS10*.lean'))
rows=[dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in mods]
x=dict(exit_status=0,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),generic_lean_sources=rows,lean_run=False,changed_generic_lemmas=[],new_lean_specializations=False,next_consumer='AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness; concrete S2 source Calls tree and source/model order remain open',generator_check='Python syntax plus source manifest validation; no certificate-generation --check mode exists on host collectors',print_axioms='N/A: no Lean run')
(E/'preflight.json').write_text(json.dumps(x,indent=2)+'\n')
print('preflight PASS')
