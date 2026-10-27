import FJe_FullNonlinear
import FJe_ExternalPackedValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_FullPackedValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- Complete SAME-call interpolated-full packed VALUE,with actual selected
width16 local weights and all actual table rows. -/
theorem value (s l : State) (out : Array NQ 4#usize)
    (hs : canonical s) (hl : canonical l)
    (run : state_only_poseidon.interpolated_full_pair_packed s l=ok out) :
    canonical out ∧ decoded out=fun g=>R0P.poseidonPackingFormula iBasis uBasis
      (fun j=>R0P.poseidonInterpolatedFullPair (decoded s) (decoded l)
        (FJe_ExternalAdjoint.lane g j)) := by
  obtain ⟨n,cn,vn,called⟩ := FJe_FullNonlinear.value s l out hs hl run
  have v := FJe_ExternalPackedValue.value n out cn called
  refine ⟨v.1,v.2.trans ?_⟩
  funext g
  apply congrArg (R0P.poseidonPackingFormula iBasis uBasis)
  funext j
  exact congrFun ((congrArg R0P.poseidonExternalLinear vn).trans
    (FJe_FullNonlinear.literal s l)) (FJe_ExternalAdjoint.lane g j)
#print axioms value
end AspisR1.FJe_FullPackedValue
end
