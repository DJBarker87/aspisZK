import PV_RJ4IDB_FieldR
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_FieldQMul
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev source := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul

theorem complete (a b : Q) : source a b = qMul a b := by
 simp only [source,ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul,
 PV_ProverRwP7CurrentComplexBridge.mul,PV_ProverRwP7CurrentComplexBridge.add,
 PV_ProverRwP7CurrentComplexBridge.sub,PV_RJ4IDB_FieldR.complete,
 AspisR1ProducerRelease47.field.QM31.mul,qMul,mapResult_bind,
 bind_assoc_eq,bind_tc_ok,toQ,fromQ,native_c_roundtrip]
#print axioms complete
end R1Z.PV_RJ4IDB_FieldQMul
