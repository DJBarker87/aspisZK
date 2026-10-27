import PV_B3_FieldQMul
import PV_B3_FieldQSquare
namespace PV_B3_PowerTransport
open Aeneas Aeneas.Std Result PV_B3_FieldTransport PV_B3_FieldBind
set_option autoImplicit false
 def reference (x : Old.Q) : Result Old.Q := do
  let x2 ← R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square x
  let x4 ← R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square x2
  let x8 ← R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square x4
  let x16 ← R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square x8
  let q ← R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul x16 x8
  R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul q x2
 theorem source (x : New.Q) :
    map toQ (PV_B3_Copy_117.host_arithmetic.mask_power_26 x) = reference (toQ x) := by
  simp only [PV_B3_Copy_117.host_arithmetic.mask_power_26,reference,
    ← PV_B3_FieldQSquare.source,← PV_B3_FieldQMul.source,bind_map,map_bind,map_ok]
#print axioms reference
#print axioms source
end PV_B3_PowerTransport
