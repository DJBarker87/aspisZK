import RPv_FJe_ThreeLimb
set_option autoImplicit false
namespace AspisR1.FJe_ThreeLimbTotal
open Aeneas Aeneas.Std Result FIq_Native
open AspisV8R17.RawReducer (P)
/-- Totality and value of the same actual interpolation scalar call. -/
theorem value (w0 w1 w2 c0 c1 c2 : U32)
    (hw0 : w0.val<P) (hw1 : w1.val<P) (hw2 : w2.val<P)
    (hc0 : c0.val<P) (hc1 : c1.val<P) (hc2 : c2.val<P) :
    ∃ out : U32,
      state_only_poseidon.interpolate_three_constant_limb w0 w1 w2 c0 c1 c2=ok out ∧
      out.val<P ∧ (out.val : FJe_ThreeLimb.M)=
        (w0.val : FJe_ThreeLimb.M)*(c0.val : FJe_ThreeLimb.M)+
        (w1.val : FJe_ThreeLimb.M)*(c1.val : FJe_ThreeLimb.M)+
        (w2.val : FJe_ThreeLimb.M)*(c2.val : FJe_ThreeLimb.M) := by
  obtain ⟨out,run,_,_⟩ := FJe_ThreeLimb.source_success w0 w1 w2 c0 c1 c2
    hw0 hw1 hw2 hc0 hc1 hc2
  exact ⟨out,run,FJe_ThreeLimb.model w0 w1 w2 c0 c1 c2
    hw0 hw1 hw2 hc0 hc1 hc2 out run⟩
#print axioms value
end AspisR1.FJe_ThreeLimbTotal
