import FIr_NativeValue
import ExtractedMaskPreparedMul
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIt_PreparedNew
open Aeneas Aeneas.Std Result
open FIr_NativeArithmetic
open FIo_FieldBridge (map map_bind map_ok)
abbrev NP := FIq_Native.field.PreparedQm31Multiplier
abbrev PP := AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier
def prepared (p : NP) : PP := ⟨p.components⟩
theorem component (x : NC) :
    FIq_Native.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call () x =
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call () (cm x) := by
  simp only [FIq_Native.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    cm,m31_add]
theorem mapped (x : NQ) : map prepared (FIq_Native.field.PreparedQm31Multiplier.new x)=
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new (qm x) := by
  simp only [FIq_Native.field.PreparedQm31Multiplier.new,
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new,prepared,qm,
    map_bind,map_ok,component,← FIr_NativeCM.add,bind_map]
theorem valid (x : NQ) (p : NP) (hx : FIr_NativeValue.Canon x)
    (run : FIq_Native.field.PreparedQm31Multiplier.new x=ok p) :
    ExtractedMaskPreparedState.PreparedFor (prepared p) (qm x) := by
  obtain ⟨p',hp,hvalid⟩ := ExtractedMaskPreparedState.current_prepared_new (qm x) hx
  have same := mapped x
  rw [run,map_ok,hp] at same
  exact Result.ok.inj same ▸ hvalid
#print axioms component
#print axioms mapped
#print axioms valid
end AspisR1.FIt_PreparedNew
end
