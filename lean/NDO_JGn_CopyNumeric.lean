import NDO_JGn_CopyFold
import NDO_JGn_CopyPatterns
import NDO_JGn_ActiveNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyNumeric
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (cells)
open pool_v1.pair_forest_copy_terminal

def helper : field.QM31 := FIq_Carriers.toQ JFu_ClaimsData.q026
def residual : field.QM31 := cells JGl_NumericData.copy ⟨0,by decide⟩

theorem helperCanonical : Canon helper := by
  change (1520023580<2147483647 ∧ 1972807226<2147483647) ∧ (213458520<2147483647 ∧ 1570606483<2147483647)
  omega
#print axioms helperCanonical

theorem residualCanonical : Canon residual := by
  change (1411961913<2147483647 ∧ 328236180<2147483647) ∧ (2139569287<2147483647 ∧ 2133865436<2147483647)
  omega
#print axioms residualCanonical

theorem model : decode JGn_ActiveData.a64 * R0P.copyResidual JGn_CopyRows.row136
    (decode helper) (decode JFu_TerminalPrefix.challenges.chi)=decode residual := by
  jgl_words
#print axioms model

theorem identified (copy : PoolV1PairForestCompiledCopyTerminalV1)
    (run : evaluate_with_selectors JGl_NumericData.a helper JGl_NumericData.selectors
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index .PrivateTransfer=ok copy) :
    copy.residual=residual ∧ copy.active=JGn_ActiveData.a64 := by
  obtain ⟨patterns,rp,cp,ra,ca,cr,value⟩ := FJk_CopyRawValue.value JGl_NumericData.a helper
    JGl_NumericData.selectors JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
    JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index .PrivateTransfer copy
    JGl_NumericCanonical.a helperCanonical JGl_NumericCanonical.high JGl_NumericCanonical.low
    JGa_ChallengeCanonical.lambda JGa_ChallengeCanonical.chi run
  have ep := JGn_CopyPatterns.identified patterns rp
  have ea : copy.active=JGn_ActiveData.a64 := Result.ok.inj (ra.symm.trans JGn_ActiveNumeric.source)
  rw [ep,ea,JGn_CopyFold.value] at value
  exact ⟨JGb_DecodeInjective.source copy.residual residual cr residualCanonical (value.trans model),ea⟩
#print axioms identified
end AspisR1.JGn_CopyNumeric
end
