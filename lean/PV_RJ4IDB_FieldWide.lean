import PV_RJ4IDB_FieldQMul
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_FieldWide
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
/-- Deployed mul_u: multiply the second quartic coordinate by 2+i,
then preserve the original first coordinate in the second slot. -/
def mulU (a : Q) : Result Q := do
 let c ← PV_RJ4IDB_FieldR.source a.c1
 ok ⟨c,a.c0⟩

/-- Complete deployed Karatsuba WideExact::mul in source order. -/
def mul (a b : W) : Result W := do
 let ac ← PV_RJ4IDB_FieldQMul.source a.c0 b.c0
 let bd ← PV_RJ4IDB_FieldQMul.source a.c1 b.c1
 let l ← PV_RJ4IDB_FieldQ.S.qadd a.c0 a.c1
 let r ← PV_RJ4IDB_FieldQ.S.qadd b.c0 b.c1
 let cross ← PV_RJ4IDB_FieldQMul.source l r
 let u ← mulU bd
 let c0 ← PV_RJ4IDB_FieldQ.S.qadd ac u
 let t ← PV_RJ4IDB_FieldQ.S.qsub cross ac
 let c1 ← PV_RJ4IDB_FieldQ.S.qsub t bd
 ok ⟨c0,c1⟩

theorem mulU_complete (a : Q) : mulU a = mapResult fromQ
 (AspisR1ProducerRelease47.field.wide_exact.mul_u (toQ a)) := by
 simp only [mulU,PV_RJ4IDB_FieldR.complete,
 AspisR1ProducerRelease47.field.wide_exact.mul_u,mapResult_bind,
 bind_assoc_eq,bind_tc_ok,toQ,fromQ,toC,fromC]

theorem complete (a b : W) : mul a b = wMul a b := by
 simp only [mul,PV_RJ4IDB_FieldQMul.complete,PV_RJ4IDB_FieldQ.add,
 PV_RJ4IDB_FieldQ.sub,mulU_complete,wMul,qMul,qAdd,qSub,
 AspisR1ProducerRelease47.field.wide_exact.WideExact.mul,
 mapResult_bind,bind_assoc_eq,bind_tc_ok,toW,fromW,toQ,fromQ,
 native_q_roundtrip,native_c_roundtrip]
#print axioms mulU_complete
#print axioms complete
end R1Z.PV_RJ4IDB_FieldWide
