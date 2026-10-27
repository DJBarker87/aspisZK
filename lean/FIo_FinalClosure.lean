import FIo_PowersCanonical
import FIo_ConcreteDictionary
import FIo_Nonvacuity
import FIn_QuarterAlias
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_FinalClosure
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

/-- A source composition on one actual result. This is a canonicality result,
not the still-open model value law for all seven Pair components. -/
theorem grouped_after_powers (alpha : NE) (f : Slice U8) (result : NE)
    (ha : FIo_WideValues.Canon alpha)
    (run : (do
      let low ← FIo_Native.weights.powers 16#usize alpha
      FIo_Native.weights.s2_grouped_inactive_pair f low)=ok result) :
    FIo_WideValues.Canon result ∧
      CheckpointBytes5Output.ofE (FIo_Install.fromE result)=
        AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide result) := by
  obtain ⟨low,hlow,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact ⟨FIo_GroupCanonical.canonical f low result
    (FIo_PowersCanonical.canonical 16#usize alpha low ha hlow) run,
    FIo_ConcreteDictionary.decoded result⟩

#print axioms grouped_after_powers
#print axioms AspisR1.FIo_Nonvacuity.same_result
#print axioms AspisR1.FIn_QuarterAlias.field_type
end AspisR1.FIo_FinalClosure
end
