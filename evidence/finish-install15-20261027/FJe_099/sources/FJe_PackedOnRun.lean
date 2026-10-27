import FJe_PackedValues
import FJa_PoseidonOrigins
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedOnRun
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- The actual projected evaluator reaches the proved leading and full packed
VALUES on the SAME openings and selector operands. No independently selected
packed results are premises. This does not claim an internal-pair VALUE. -/
theorem value (o : Openings) (s : Selectors) (out : Array NQ 4#usize)
    (hz : canonical o.z) (hx : canonical o.xor12_z) (hs : canonical s.local)
    (run : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected o s=ok out) :
    ∃ (leading full : Array NQ 4#usize),
      state_only_poseidon.leading_pair_packed o=ok leading ∧
      state_only_poseidon.interpolated_full_pair_packed o.z s.local=ok full ∧
      canonical leading ∧ canonical full ∧
      decoded leading=(fun g=>R0P.poseidonPackingFormula iBasis uBasis
        (fun j=>R0P.poseidonLeadingPair (decoded o.z) (decoded o.xor12_z)
          (FJe_ExternalAdjoint.lane g j))) ∧
      decoded full=(fun g=>R0P.poseidonPackingFormula iBasis uBasis
        (fun j=>R0P.poseidonInterpolatedFullPair (decoded o.z) (decoded s.local)
          (FJe_ExternalAdjoint.lane g j))) := by
  obtain ⟨_,_,_,l,f,_,_,_,_,_,_,rl,rf,_⟩ := FJa_PoseidonOrigins.reached o s out run
  have vl := FJe_PackedValues.leading o l hz hx rl
  have vf := FJe_PackedValues.full o.z s.local f hz hs rf
  exact ⟨l,f,rl,rf,vl.1,vf.1,vl.2,vf.2⟩
#print axioms value
end AspisR1.FJe_PackedOnRun
end
