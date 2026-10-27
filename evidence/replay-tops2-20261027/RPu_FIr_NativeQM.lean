import RPu_FIr_NativeCM
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_NativeQM
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (map map_bind map_ok)
open FIr_NativeArithmetic

theorem add (x y : NQ) : map qm (FIq_Native.field.QM31.add x y)=
    AspisR1SelectedMaskProbe.field.QM31.add (qm x) (qm y) := by
  simp only [FIq_Native.field.QM31.add,AspisR1SelectedMaskProbe.field.QM31.add,qm,
    ← FIr_NativeCM.add,bind_map,map_bind,map_ok]

theorem mul (x y : NQ) : map qm (FIq_Native.field.QM31.mul x y)=
    AspisR1SelectedMaskProbe.field.QM31.mul (qm x) (qm y) := by
  simp only [FIq_Native.field.QM31.mul,AspisR1SelectedMaskProbe.field.QM31.mul,qm,
    ← FIr_NativeCM.mul,← FIr_NativeCM.add,← FIr_NativeCM.sub,← FIr_NativeCM.by_r,
    bind_map,map_bind,map_ok]

#print axioms add
#print axioms mul
end AspisR1.FIr_NativeQM
end
