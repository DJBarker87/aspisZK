import NDO_JGj_LeadingTotal
import NDO_JGj_FullTotal
import RPv_FJe_PackedValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_PackedTwo
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings Selectors)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- The SAME operands jointly have actual successful canonical leading/full
calls and the imported exact FJe values. Neither successful call is a premise. -/
theorem source (o : Openings) (s : Selectors)
    (hz : canonical o.z) (hx : canonical o.xor12_z) (hl : canonical s.local) :
    ∃ leading full,
      state_only_poseidon.leading_pair_packed o=ok leading ∧
      state_only_poseidon.interpolated_full_pair_packed o.z s.local=ok full ∧
      canonical leading ∧ canonical full ∧
      decoded leading=(fun g=>R0P.poseidonPackingFormula iBasis uBasis
        (fun j=>R0P.poseidonLeadingPair (decoded o.z) (decoded o.xor12_z)
          (FJe_ExternalAdjoint.lane g j))) ∧
      decoded full=(fun g=>R0P.poseidonPackingFormula iBasis uBasis
        (fun j=>R0P.poseidonInterpolatedFullPair (decoded o.z) (decoded s.local)
          (FJe_ExternalAdjoint.lane g j))) := by
  obtain ⟨leading,rl,_⟩ := JGj_LeadingTotal.source o hz hx
  obtain ⟨full,rf,_⟩ := JGj_FullTotal.source o.z s.local hz hl
  have vl := FJe_PackedValues.leading o leading hz hx rl
  have vf := FJe_PackedValues.full o.z s.local full hz hl rf
  exact ⟨leading,full,rl,rf,vl.1,vf.1,vl.2,vf.2⟩
#print axioms source
end AspisR1.JGj_PackedTwo
end
