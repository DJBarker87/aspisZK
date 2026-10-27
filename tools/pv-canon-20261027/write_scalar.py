from pathlib import Path
D=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
items=[('Mul','mul','(x y : U32)','', 'mul_exact x y'),('Add','add','(x y : U32) (hx : M x) (hy : M y)','', 'add_exact x y hx hy'),('Sub','sub','(x y : U32) (hx : M x) (hy : M y)','', 'sub_exact x y hx hy')]
for name,op,args,_,proof in items:
 (D/f'PV_Canon_{name}.lean').write_text(f'''import R1Z.PV_Canon_Reduce
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
theorem current_{op} {args} : ∃ z, S.{op} x y = .ok z ∧ M z := by
  rw [ProverRwP7CurrentBaseBridge.{op}]
  obtain ⟨z,hz,hc,_⟩ := ProverCommitM31Ops48.{proof}
  exact ⟨z,hz,hc⟩
#print axioms current_{op}
end R1Z.PV_Canon
''')
