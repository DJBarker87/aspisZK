import RPu_FIq_Native07
import RPv_FJa_SquareValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PoseidonPow5
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
/-- Native S-box primitive required by leading/full/internal round VALUES. -/
theorem value (x out : NQ) (hx : Canon x)
    (run : state_only_poseidon.pow5 x=ok out) : Canon out ∧ decode out=decode x^5 := by
  unfold state_only_poseidon.pow5 at run
  obtain ⟨x2,h2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨x4,h4,run⟩ := FIv_Map.bind_success _ _ _ run
  have v2 := FJa_SquareValue.value x x2 hx h2
  have v4 := FJa_SquareValue.value x2 x4 v2.1 h4
  have v5 := FIv_NativeValue.mul x4 x out v4.1 hx run
  refine ⟨v5.1,?_⟩
  rw [v5.2,v4.2,v2.2]
  ring
#print axioms value
end AspisR1.FJa_PoseidonPow5
end
