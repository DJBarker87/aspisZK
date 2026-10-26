"""Retain the actual emitted pole leaves with structural carrier aliases."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p8'
s=(e/'pole-leaf-Funs.lean.txt').read_text();a=s.index('/-- [aspis_r1_cost_probe::ct_pole::equal]');b=s.index('\nend PV_PoleLeaf',a)
out='import R1Z.PV_CurrentScaleInstall\nset_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_PoleLeafSource\nopen Aeneas Aeneas.Std Result ControlFlow Error\nabbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31\n'+s[a:b]+'''

theorem equal_total (a b : aspis_core.field.QM31) :
    ∃ answer, ct_pole.equal a b = ok answer := by
  simp only [ct_pole.equal,lift,bind_tc_ok]
  exact ⟨_,rfl⟩
#print axioms equal_total
end R1Z.PV_PoleLeafSource
'''
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_PoleLeafSource.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:
 p.write_text(out)
 (e/'pole-leaf-source-map.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Exact emitted bodies; nominal QM31 alias. Generated option/header omission; no backend edits.'),indent=2)+'\n')
