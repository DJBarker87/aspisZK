import S9NativePushProductSumV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9NativePushNewProductV1
open AspisR1S9PushByteProductsReaderCallsV1 (Dot)
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9NativePushProductSumV1
open AspisR1S9NativePushRangeTraceV1
open AspisR1FastDotsPushProductTraceRootV1
open AspisR1FastDotsTailFieldProductRootV1

/-- The actual current constructor produces exactly the EXISTING source zero
state through the reserved coordinate map. -/
theorem native_new_source_zero (dot : Dot) (hnew : fast_pairing.EbyKDot.new=.ok dot) :
    toSourceState dot=EbyKNewToPushStateABI.pushZero := by
  unfold fast_pairing.EbyKDot.new fast_pairing.canonical.Dot.new at hnew
  simp only [bind_tc_ok] at hnew
  have he := Result.ok.inj hnew
  rw [←he]
  rfl

/-- Reuses the existing initialized-source-state bound shape. Only four zero
coordinates are inspected; no field recurrence is evaluated. -/
theorem source_zero_invariants :
    AspisR1DotCountBoundV1.sumsBelowCount
      EbyKNewToPushStateABI.pushZero.count.val EbyKNewToPushStateABI.pushZero.c0.sums ∧
    AspisR1DotCountBoundV1.sumsBelowCount
      EbyKNewToPushStateABI.pushZero.count.val EbyKNewToPushStateABI.pushZero.c1.sums := by
  have h0 : AspisR1DotCountBoundV1.sumsBelowCount
      EbyKNewToPushStateABI.pushZero.count.val EbyKNewToPushStateABI.pushZero.c0.sums := by
    intro j hj
    have hcases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hcases with h | h | h | h <;> subst j <;>
      simp [EbyKNewToPushStateABI.pushZero,AspisR1DotCountBoundV1.sumsBelowCount]
  exact ⟨h0,h0⟩

/-- Same actual new+byte-product run has the existing decoded ordered product
sum, without any externally supplied accumulator-history or input Can premise. -/
theorem actual_new_push_products_decoded_sum
    (bytes : Slice U8) (scratch : Slice aspis_core.field.QM31)
    (n : Usize) (dot out : Dot)
    (hnew : fast_pairing.EbyKDot.new=.ok dot)
    (hdiv : (Slice.len bytes /32#usize : Result Usize)=.ok n)
    (hrun : weights.push_byte_products dot bytes scratch n=.ok (.Ok (),out)) :
    ∃ (js : List Usize) (xs : Inputs),
      Trace bytes scratch n {start:=0#usize,«end»:=n} dot js out ∧
      js.length=n.val ∧
      List.Forall₂ (fun j p => ∃ w q,
        weights.field bytes j=.ok w ∧ Slice.index_usize scratch j=.ok q ∧
        p=(toSourceWide w,toSourceQ q)) js xs ∧
      decodeState (stateValue (toSourceState out))=productSum xs := by
  have hz := native_new_source_zero dot hnew
  have hi := source_zero_invariants
  have h0 : AspisR1DotCountBoundV1.sumsBelowCount
      (toSourceState dot).count.val (toSourceState dot).c0.sums := by rw [hz]; exact hi.1
  have h1 : AspisR1DotCountBoundV1.sumsBelowCount
      (toSourceState dot).count.val (toSourceState dot).c1.sums := by rw [hz]; exact hi.2
  obtain ⟨js,xs,htrace,hlen,hcorr,hd⟩ := actual_loop_decoded_product_sum
    bytes scratch n {start:=0#usize,«end»:=n} dot out hdiv rfl (by change 0 ≤ n.val; omega)
    hrun h0 h1
  have hlen' : js.length=n.val := by simpa using hlen
  rw [hz,decode_zero_state,zero_add] at hd
  exact ⟨js,xs,htrace,hlen',hcorr,hd⟩

#print axioms native_new_source_zero
#print axioms source_zero_invariants
#print axioms actual_new_push_products_decoded_sum
end AspisR1S9NativePushNewProductV1
