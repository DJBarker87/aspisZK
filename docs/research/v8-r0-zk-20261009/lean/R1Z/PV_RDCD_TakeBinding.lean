import R1Z.PV_RDCD_V169Raw
import R1Z.PV_RDCD_Defaults194
import R1Z.PV_CB_TakeRef
import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
namespace R1Z.PV_RDCD_TakeBinding
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RDCD_Defaults194
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op3 := @PV_RDCD_V169.core.mem.take}
/-- Both outputs include the original owned carrier and the replacement. -/
theorem original_reference (ops : ExternalFuns) {T : Type} (inst : core.default.Default T) (x : T) :
    (selected ops).op3 inst x = PV_CB_TakeRef.reference.take inst x := rfl

theorem vector_m31 (ops : ExternalFuns) (x : alloc.vec.Vec aspis_core.field.M31) :
    (selected ops).op3 (vecDefault aspis_core.field.M31) x = ok (x,alloc.vec.Vec.new _) := rfl

theorem vector_qm31 (ops : ExternalFuns) (x : alloc.vec.Vec aspis_core.field.QM31) :
    (selected ops).op3 (vecDefault aspis_core.field.QM31) x = ok (x,alloc.vec.Vec.new _) := rfl

theorem array10 (ops : ExternalFuns) (x : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) :
    (selected ops).op3 (arrayDefault aspis_core.field.M31 10#usize) x =
      ok (x,emptyVectors aspis_core.field.M31 10#usize) := rfl

theorem array16 (ops : ExternalFuns) (x : Array (alloc.vec.Vec aspis_core.field.M31) 16#usize) :
    (selected ops).op3 (arrayDefault aspis_core.field.M31 16#usize) x =
      ok (x,emptyVectors aspis_core.field.M31 16#usize) := rfl

theorem error {T : Type} (inst : core.default.Default T) (x : T) (e : Error)
    (h : inst.default = fail e) : PV_RDCD_V169.core.mem.take inst x = fail e := by
  simp [PV_RDCD_V169.core.mem.take,h]

theorem divergence {T : Type} (inst : core.default.Default T) (x : T)
    (h : inst.default = div) : PV_RDCD_V169.core.mem.take inst x = div := by
  simp [PV_RDCD_V169.core.mem.take,h]
#print axioms original_reference
#print axioms vector_m31
#print axioms vector_qm31
#print axioms array10
#print axioms array16
#print axioms error
#print axioms divergence
end R1Z.PV_RDCD_TakeBinding
