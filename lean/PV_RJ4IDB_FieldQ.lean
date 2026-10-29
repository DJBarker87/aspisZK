import R1Z.PV_ProverRwP7CurrentComplexBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_FieldQ
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
namespace S
abbrev cadd := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add
abbrev csub := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub
abbrev cmul := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul
abbrev qadd := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
/-- Deployed QM31::sub, including ordered component stores. -/
def qsub (a b : Q) : Result Q := do
 let c ← csub a.c0 b.c0
 let d ← csub a.c1 b.c1
 ok ⟨c,d⟩
end S

theorem add (a b : Q) : S.qadd a b = qAdd a b := by
 simp only [S.qadd,ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add,
 PV_ProverRwP7CurrentComplexBridge.add,AspisR1ProducerRelease47.field.QM31.add,
 qAdd,mapResult_bind,bind_assoc_eq,bind_tc_ok,toQ,fromQ]

theorem sub (a b : Q) : S.qsub a b = qSub a b := by
 simp only [S.qsub,S.csub,PV_ProverRwP7CurrentComplexBridge.sub,
 AspisR1ProducerRelease47.field.QM31.sub,qSub,mapResult_bind,
 bind_assoc_eq,bind_tc_ok,toQ,fromQ]
#print axioms add
#print axioms sub
end R1Z.PV_RJ4IDB_FieldQ
