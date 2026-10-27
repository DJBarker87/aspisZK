import RPv_FJe_LeadingPrefix
import RPv_FJe_M31PackedNonlinear
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_LeadingNonlinear
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings)
def nonlinear (o : Openings) := fun j : Fin (16#usize).val=>
  R0P.poseidonPow5
    (R0P.poseidonFullRound (R0P.poseidonExternalLinear (FJe_LeadingPrefix.absorbed o))
      (R0P.poseidonExternalInitial 0) j+R0P.poseidonExternalInitial 1 j)
/-- The final packed-layer input on the original leading call has a complete
symbolic value. This is an input value, not the still-open packed output. -/
theorem value (o : Openings) (out : Array NQ 4#usize)
    (hz : canonical o.z) (hx : canonical o.xor12_z)
    (run : state_only_poseidon.leading_pair_packed o=ok out) :
    ∃ n : Array NQ 16#usize,canonical n ∧ decoded n=nonlinear o ∧
      state_only_poseidon.external_linear_packed n=ok out := by
  obtain ⟨middle,cm,vm,tail⟩ := FJe_LeadingPrefix.value o out hz hx run
  obtain ⟨n,cn,vn,called⟩ := FJe_M31PackedNonlinear.value middle
    (FJb_InitialConstants.row 1) out cm (FJb_InitialConstants.bounded 1) tail
  refine ⟨n,cn,?_,called⟩
  apply vn.trans
  funext j
  change R0P.poseidonPow5 (_+_)=R0P.poseidonPow5 (_+_)
  apply congrArg R0P.poseidonPow5
  exact congrArg₂ (·+·) (congrFun vm j) (FJb_InitialConstants.model 1 j)
/-- Only the mathematical external map is unfolded; no native recurrence is
reduced to establish the literal leading pair's final state. -/
theorem literal (o : Openings) :
    R0P.poseidonExternalLinear (nonlinear o)=
      R0P.poseidonLeadingPair (decoded o.z) (decoded o.xor12_z) := by
  rfl
#print axioms value
#print axioms literal
end AspisR1.FJe_LeadingNonlinear
end
