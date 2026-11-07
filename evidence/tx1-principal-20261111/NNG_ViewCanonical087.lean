import NNG_ViewShape087
import LIBC_PreparedDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ViewCanonical087
open Aeneas Aeneas.Std NMP_prepare

theorem limbs (proof semantic y1 : Slice U8) (bound : 10055≤proof.val.length)
 (values : StrictWideByteCodec.WideLimbs) :
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative
  (AspisR1SelectedWideViewV1.preparedView (NHF_ViewFinish.value proof semantic y1
   (AspisR1SelectedWideViewV1.parserCarrier (CandidateWideParserRefinement.limbsToCandidate values)) bound)).inactive) := by
 refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,⟨⟨?_,?_⟩,⟨?_,?_⟩⟩⟩
 all_goals
   change (M31ParserRefinement.valueToU32 _).val<2147483647
   rw [M31ParserRefinement.valueToU32_val]
 all_goals first
 | exact (values.1 0).isLt
 | exact (values.1 1).isLt
 | exact (values.1 2).isLt
 | exact (values.1 3).isLt
 | exact (values.2 0).isLt
 | exact (values.2 1).isLt
 | exact (values.2 2).isLt
 | exact (values.2 3).isLt

theorem returned (proof semantic y1 : Slice U8) (bound : 10055≤proof.val.length) (v : verifier.View)
 (success : NNG_WideView087.call proof semantic y1=.ok (.Ok v)) :
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative (NNG_PrepareCarriers087.view v).inactive) := by
 obtain ⟨values,_,same⟩ := NNG_ViewShape087.shape proof semantic y1 bound v success
 subst v
 rw [NNG_PrepareCarriers087.viewBack_inverse]
 exact limbs proof semantic y1 bound values
#print axioms limbs
#print axioms returned
end AspisR1.NNG_ViewCanonical087
