import FJk_ResidualPack
import FJh_PoseidonOnComposition
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_Native07Value
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- Complete native value on the actual evaluator run, now in scalarResidual form. -/
theorem value (o : Openings) (s : Selectors) (out : Array NQ 4#usize)
    (hz : canonical o.z) (ht : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hs : canonical s.local) (hb : Canon s.block)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out) :
    canonical out ∧ decoded out=fun g=>R0P.poseidonPackingFormula iBasis uBasis
      (fun j=>R0P.poseidonScalarResidual (FJh_Native07RawValue.openings o)
        (decode s.block) (decoded s.local) (FJe_ExternalAdjoint.lane g j)) := by
  have v := FJh_Native07RawValue.value o s out hz ht hx hs hb run
  refine ⟨v.1,v.2.trans ?_⟩
  funext g
  exact FJk_ResidualPack.value o s g
#print axioms value
end AspisR1.FJk_Native07Value
end
