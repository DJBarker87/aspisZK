import FJe_LeadingNonlinear
import FJe_ExternalPackedValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_LeadingPackedValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- Complete SAME-call leading packed VALUE,including its actual final
external layer. No final-output value is an input premise. -/
theorem value (o : Openings) (out : Array NQ 4#usize)
    (hz : canonical o.z) (hx : canonical o.xor12_z)
    (run : state_only_poseidon.leading_pair_packed o=ok out) :
    canonical out ∧ decoded out=fun g=>R0P.poseidonPackingFormula iBasis uBasis
      (fun j=>R0P.poseidonLeadingPair (decoded o.z) (decoded o.xor12_z)
        (FJe_ExternalAdjoint.lane g j)) := by
  obtain ⟨n,cn,vn,called⟩ := FJe_LeadingNonlinear.value o out hz hx run
  have v := FJe_ExternalPackedValue.value n out cn called
  refine ⟨v.1,v.2.trans ?_⟩
  funext g
  apply congrArg (R0P.poseidonPackingFormula iBasis uBasis)
  funext j
  exact congrFun ((congrArg R0P.poseidonExternalLinear vn).trans
    (FJe_LeadingNonlinear.literal o)) (FJe_ExternalAdjoint.lane g j)
#print axioms value
end AspisR1.FJe_LeadingPackedValue
end
