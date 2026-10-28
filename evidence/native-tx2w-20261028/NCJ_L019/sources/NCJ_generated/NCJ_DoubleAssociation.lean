import NCJ_CallLog
import FJr_DoubleValue
set_option autoImplicit false
noncomputable section
namespace NCJ_DoubleAssociation
open Aeneas Aeneas.Std Result AspisR1
abbrev Q := FIo_Native.aspis_core.field.QM31
/-- Literal frozen double, preserving both multiplication call sites. -/
def sourcePort (x : Q) : Result Q := do
  let a ← FIo_Native.aspis_core.field.QM31.mul x x
  let b ← FIo_Native.aspis_core.field.QM31.mul x x
  let c ← FIo_Native.aspis_core.field.QM31.add a b
  FIo_Native.aspis_core.field.QM31.sub c FIo_Native.aspis_core.field.QM31.ONE

def sharedPort (x : Q) : Result Q := do
  let a ← FIo_Native.aspis_core.field.QM31.mul x x
  let c ← FIo_Native.aspis_core.field.QM31.add a a
  FIo_Native.aspis_core.field.QM31.sub c FIo_Native.aspis_core.field.QM31.ONE

theorem sharing (x : Q) : sourcePort x = sharedPort x := by
  cases h : FIo_Native.aspis_core.field.QM31.mul x x <;>
    simp only [sourcePort,sharedPort,h,bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem constructor (x out : FIn_WeightsExtract.field.QM31)
    (run : FIn_WeightsExtract.double x=ok out) :
    sourcePort (FIo_Install.toQ x) = ok (FIo_Install.toQ out) := by
  rw [sharing]
  unfold FIn_WeightsExtract.double at run
  obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have ma := FJc_WeightQMMul.mul x x a ha
  have ab := FJc_WeightQMBridge.add a a b hb
  have su := FJc_WeightQMBridge.sub b FIn_WeightsExtract.field.QM31.ONE out run
  have one : FIo_Install.toQ FIn_WeightsExtract.field.QM31.ONE =
      FIo_Native.aspis_core.field.QM31.ONE := by
    unfold FIo_Install.toQ FIn_WeightsExtract.field.QM31.ONE FIo_Native.aspis_core.field.QM31.ONE
    rfl
  simp only [sharedPort,ma,ab,bind_tc_ok,one] at su ⊢
  exact su

#print axioms sharing
#print axioms constructor
end NCJ_DoubleAssociation
