#!/usr/bin/env python3
"""Verify exact extraction adaptations and final reference pins."""
import pathlib,subprocess,hashlib,json
H=pathlib.Path(__file__).resolve().parent;R=H.parents[3];L=H.parent/'lean/R1Z'
def fetch(s):return subprocess.check_output(['ssh','dombarker@100.108.41.90','cat '+s],text=True)
base='/home/dombarker/project-offloads/codex-cx-builder-ref8-20261021/'
raw=fetch(base+'carry/generated/Reference-entry.lean')
expected=raw.replace('import Aeneas\n','import R1Z.BuilderStdShift\n').replace('Std.U64.wrapping_shr index level','R1Z.BuilderStdModels.shift64 index level')
assert expected==(L/'BuilderTreeCarryExtracted.lean').read_text()
step=fetch(base+'projected/generated/Reference-entry.lean')
a=step.index('/-- [aspis_statement::pool_v1::incremental_merkle::tree_reference::carry_step_owned]')
assert ('import R1Z.BuilderTreeCarryExtracted\nopen Aeneas Aeneas.Std Result\nnamespace AspisBuilderTreeReference\n'+step[a:])==(L/'BuilderTreeStepExtracted.lean').read_text()
current=(R/'tools/r1-builder-reference/tree.rs').read_text()
assert current==fetch(base+'projected-source/tools/r1-builder-reference/tree.rs')
# The source's borrows are only shared reads of owned Copy values here.
# This audit records the single source slice; the Kani receipt is independent.
for f in ['BuilderTreeCarryExtracted.lean','BuilderTreeStepExtracted.lean']:
 s=(L/f).read_text()
 assert not any(t in s for t in ['axiom ','sorry','native_decide','opaque '])
def pin(s):return dict(sha256=hashlib.sha256(s.encode()).hexdigest(),size=len(s.encode()))
rec=dict(raw_carry=pin(raw),raw_step=pin(step),adapted={f:pin((L/f).read_text()) for f in ['BuilderTreeCarryExtracted.lean','BuilderTreeStepExtracted.lean']},reference=pin(current),
 changes=['Imports only plus existing proved shift64 adapter for backend usize/U32 shift mismatch','Select carry_step_owned declaration from second extraction and import the identical carry dependency; function body unchanged'],
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),unsupported_declarations=0)
(H/'builder-cont8-adaptation-audit.json').write_text(json.dumps(rec,indent=2)+'\n')
print('Exact function bodies; imports and proved shift adapter only; no external declarations')
