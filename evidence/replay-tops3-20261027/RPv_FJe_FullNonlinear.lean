import RPv_FJe_FullConstants
import RPv_FJe_QmPackedNonlinear
import RPv_FJb_QmLazyRound
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_FullNonlinear
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
def nonlinear (s l : State) := fun j : Fin (16#usize).val=>R0P.poseidonPow5
  (R0P.poseidonFullRound (decoded s) (FJe_FullConstants.even l) j+
    FJe_FullConstants.odd l j)
/-- Complete actual input VALUE of the final external packed layer in the
same interpolated-full call. No independent round output is assumed. -/
theorem value (s l : State) (out : Array NQ 4#usize)
    (hs : canonical s) (hl : canonical l)
    (run : state_only_poseidon.interpolated_full_pair_packed s l=ok out) :
    ∃ n : State,canonical n ∧ decoded n=nonlinear s l ∧
      state_only_poseidon.external_linear_packed n=ok out := by
  obtain ⟨q0,q1,q2,even,odd,middle,r0,r1,r2,re,ro,rm,tail⟩ := FJe_FullCalls.value s l out run
  have ve := FJe_FullConstants.even_value l q0 q1 q2 even hl r0 r1 r2 re
  have vo := FJe_FullConstants.odd_value l q0 q1 q2 odd hl r0 r1 r2 ro
  have vm := FJb_QmLazyRound.value s even middle hs ve.1 rm
  obtain ⟨n,cn,vn,called⟩ := FJe_QmPackedNonlinear.value middle odd out vm.1 vo.1 tail
  have em := vm.2.trans (congrArg (R0P.poseidonFullRound (decoded s)) ve.2)
  refine ⟨n,cn,vn.trans ?_,called⟩
  funext j
  apply congrArg R0P.poseidonPow5
  exact congrArg₂ (·+·) (congrFun em j) (congrFun vo.2 j)
/-- The mathematical final external layer is the SAME literal full pair. -/
theorem literal (s l : State) : R0P.poseidonExternalLinear (nonlinear s l)=
    R0P.poseidonInterpolatedFullPair (decoded s) (decoded l) := by
  rfl
#print axioms value
#print axioms literal
end AspisR1.FJe_FullNonlinear
end
