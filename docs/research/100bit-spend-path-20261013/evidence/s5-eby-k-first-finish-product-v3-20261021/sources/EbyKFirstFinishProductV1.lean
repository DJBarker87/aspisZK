import EbyKPushPairInitializedV1
import FourDotsPushProductTraceRootV1
import EbyKPushPairFinishDecodedV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S5EbyKFirstFinishProductV1
open AspisR1WeightsPairCutEbyKDotOpsV1
open AspisR1S5EbyKConcreteOpsInstanceV1
open AspisR1S5EbyKPushPairInitializedV1
open AspisR1S5EbyKPushPairForwardStateV1
open AspisR1S5EbyKPushPairFinishDecodedV1
open AspisR1S5EbyKConcreteOpsWrapperLawsV1
open AspisR1FastDotsPushProductTraceRootV1
open AspisR1FastDotsTailFieldProductRootV1
open AspisR1DotCountBoundV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps := sourceOps

/-- The installed constructor, one canonical-value push, and typed finish
implement the one-term EbyK product. This uses the exact accepted QRaw push
trace and the current finish decoder. -/
theorem first_finish_decodes_product
    (value : AspisR1WeightsPairCut.field.WideExact)
    (scalar : AspisR1WeightsPairCut.field.QM31)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
      (wideToSource value))
    (hscalar : ∀ x ∈
      (AspisR1EbyKPushDotBackend.scalarQ (qToSource scalar)).val,
      x.val < 2147483647) :
    ∃ sourceOut : AspisR1EbyKPushDotBackend.PushState,
      ∃ currentOut : AspisR1FastDotsTailFinishSourceMapV1.CurrentWide,
        AspisR1WeightsPairCut.fast_pairing.EbyKDot.new =
          .ok (stateFromSource EbyKNewToPushStateABI.pushZero) ∧
        AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
          (stateFromSource EbyKNewToPushStateABI.pushZero) value scalar =
          .ok (.Ok (), stateFromSource sourceOut) ∧
        AspisR1WeightsPairCut.fast_pairing.EbyKDot.finish
          (stateFromSource sourceOut) = .ok (wideFromSource currentOut) ∧
        AspisR1CurrentWide.Proof.decodeWide
          (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE currentOut) =
          scalarProduct (wideToSource value, qToSource scalar) := by
  obtain ⟨sourceOut,initial,hnew0,hinit,hpush,hinv0,hinv1,hcount,hupdate⟩ :=
    first_push_from_new value scalar hcanonical hscalar
  have hnew : AspisR1WeightsPairCut.fast_pairing.EbyKDot.new =
      .ok (stateFromSource EbyKNewToPushStateABI.pushZero) := by
    rw [← hinit]
    exact hnew0
  have hzero : stateToSource initial = EbyKNewToPushStateABI.pushZero := by
    rw [hinit]
    exact stateToFrom _
  have hsource : AspisR1EbyKPushDotBackend.pushWithDotBackend
      AspisR1EbyKPushDecodedProductUpdate.QRaw EbyKNewToPushStateABI.pushZero
      (wideToSource value) (qToSource scalar) = .ok (.Ok (),sourceOut) := by
    obtain ⟨sourceOut',hops,hmap⟩ := installed_push_success_map
      initial value scalar (.Ok ()) (stateFromSource sourceOut) hpush
    have hout : sourceOut' = sourceOut := by
      have := congrArg stateToSource hmap
      simpa using this
    subst sourceOut'
    simpa [sourceOps,hzero] using hops
  have htrace : AcceptedPushTrace AspisR1EbyKPushDecodedProductUpdate.QRaw
      EbyKNewToPushStateABI.pushZero
      [(wideToSource value,qToSource scalar)] sourceOut := by
    exact AcceptedPushTrace.cons _ _ _ _ _ _ hsource (AcceptedPushTrace.nil _)
  have hzero0 : sumsBelowCount EbyKNewToPushStateABI.pushZero.count.val
      EbyKNewToPushStateABI.pushZero.c0.sums := by
    intro j hj
    have hcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hcases with h | h | h | h <;> subst j <;>
      simp [EbyKNewToPushStateABI.pushZero,
        AspisR1FinishDotCountBoundV2.sumsBelowCount]
  have hzero1 : sumsBelowCount EbyKNewToPushStateABI.pushZero.count.val
      EbyKNewToPushStateABI.pushZero.c1.sums := by
    intro j hj
    have hcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hcases with h | h | h | h <;> subst j <;>
      simp [EbyKNewToPushStateABI.pushZero,
        AspisR1FinishDotCountBoundV2.sumsBelowCount]
  have hcanonicalList : ∀ p ∈ [(wideToSource value,qToSource scalar)],
      AspisR1EbyKPowerValueCanonicalToPush.pushCanonical p.1 := by
    intro p hp
    simp only [List.mem_singleton] at hp
    rcases hp with rfl
    exact hcanonical
  have htraceState := accepted_trace_product_sum EbyKNewToPushStateABI.pushZero
      sourceOut [(wideToSource value,qToSource scalar)] hzero0 hzero1
      hcanonicalList htrace
  have hdecodeState := decoded_tail_product_sum sourceOut
      [(wideToSource value,qToSource scalar)] htraceState
  obtain ⟨currentOut,hfinish,hdecoded⟩ := installed_finish_decoded_state
    (stateFromSource sourceOut)
  have hstate : stateToSource (stateFromSource sourceOut)=sourceOut := stateToFrom _
  have hdecoded' : AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE currentOut) =
      decodeState (stateValue sourceOut) := by simpa [hstate] using hdecoded
  have hpushZero : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push
      (stateFromSource EbyKNewToPushStateABI.pushZero) value scalar =
        .ok (.Ok (),stateFromSource sourceOut) := by
    rw [← hinit]
    exact hpush
  have hproduct := hdecoded'.trans hdecodeState
  have hsingle : productSum [(wideToSource value,qToSource scalar)] =
      scalarProduct (wideToSource value,qToSource scalar) := by
    simp [AspisR1FastDotsTailFieldProductRootV1.productSum]
  exact ⟨sourceOut,currentOut,hnew,hpushZero,hfinish,
    hproduct.trans hsingle⟩

#print axioms first_finish_decodes_product
end AspisR1S5EbyKFirstFinishProductV1
