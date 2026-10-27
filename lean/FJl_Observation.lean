import FJl_PairExtraction
import Port4C_QueryValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_Observation
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
/-- Invert the actual indexed call into its SAME opening/fold/comparison operands. -/
theorem reached (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geometry : verifier.QueryGeometry)
    (j : Nat)
    (run : ∃ a0 a1 b0 b1, a0.next.val=j ∧
      verifier.candidate.query_values ops proof p a0 g none geometry b0=ok (.Ok (a1,b1))) :
    ∃ a0 a1 b0 b1, a0.next.val=j ∧
      Nonempty (Port4C_QueryValues.Observation ops proof p a0 a1 g none geometry b0 b1) := by
  obtain ⟨a0,a1,b0,b1,hn,hcall⟩ := run
  exact ⟨a0,a1,b0,b1,hn,Port4C_QueryValues.observed ops proof p a0 a1 g none geometry b0 b1 hcall⟩
#print axioms reached
end AspisR1.FJl_Observation
end
