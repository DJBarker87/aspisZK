import NDO_JGb_MainTotal
import NDO_JGb_Terminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_MaskedArithmetic
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic FIp_SemanticValues
open AspisR1PublicPreparation

def run (terminal mask : MQ) : Result MQ := do
  let weighted ← FIp_SemanticArithmetic.mul JFm_Begin.challenges.eta terminal
  let sum ← FIp_SemanticArithmetic.add mask weighted
  let q ← Array.index_usize JFu_ClaimsData.a3 28#usize
  FIp_SemanticArithmetic.add sum q

theorem eta : Canon JFm_Begin.challenges.eta := by
  change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647)
  decide
#print axioms eta

theorem read : Array.index_usize JFu_ClaimsData.a3 28#usize=ok JFu_ClaimsData.q115 := by rfl
#print axioms read

theorem last : Canon JFu_ClaimsData.q115 := by
  change (_<2147483647 ∧ _<2147483647) ∧ (_<2147483647 ∧ _<2147483647)
  decide
#print axioms last

/-- Executes the three arithmetic calls at the actual masked-terminal gate.
It does not assert equality to the final running value. -/
theorem source (terminal mask : MQ) (ht : Canon terminal) (hm : Canon mask) :
    ∃ out,run terminal mask=ok out ∧ Canon out ∧
      decode out=decode mask+decode JFm_Begin.challenges.eta*decode terminal+decode JFu_ClaimsData.q115 := by
  obtain ⟨weighted,hw,hwc,hwv⟩ := JGb_MainTotal.mul _ terminal eta ht
  obtain ⟨sum,hs,hsc,hsv⟩ := JGb_MainTotal.add mask weighted hm hwc
  obtain ⟨out,ho,hoc,hov⟩ := JGb_MainTotal.add sum JFu_ClaimsData.q115 hsc last
  refine ⟨out,?_,hoc,?_⟩
  · unfold run
    rw [hw,bind_tc_ok,hs,bind_tc_ok,read,bind_tc_ok,ho]
  · rw [hov,hsv,hwv]
#print axioms source
end AspisR1.JGb_MaskedArithmetic
end
