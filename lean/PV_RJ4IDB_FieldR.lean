import PV_RJ4IDB_FieldQ
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_FieldR
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev source := ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r

theorem complete (x : C) : source x = mapResult fromC
 (AspisR1ProducerRelease47.field.mul_by_r (toC x)) := by
 simp only [source,ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r,
 ProverRwP7CurrentBaseBridge.double,ProverRwP7CurrentBaseBridge.sub,
 ProverRwP7CurrentBaseBridge.add,AspisR1ProducerRelease47.field.mul_by_r,
 mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC]
#print axioms complete
end R1Z.PV_RJ4IDB_FieldR
