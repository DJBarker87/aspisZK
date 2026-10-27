import RPt_FIo_FromBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_FieldCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem field (bytes : Slice U8) (i : Usize) (z : NE)
    (run : FIo_Native.weights.field bytes i=ok z) : FIo_WideValues.Canon z := by
  unfold FIo_Native.weights.field at run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨s,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some v =>
    have same : v=z := Result.ok.inj run
    subst z
    exact FIo_FromBytes.canonical s v ho

#print axioms field
end AspisR1.FIo_FieldCanonical
end
