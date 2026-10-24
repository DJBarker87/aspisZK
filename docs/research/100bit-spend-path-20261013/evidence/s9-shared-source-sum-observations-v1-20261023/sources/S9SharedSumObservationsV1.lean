import S9PartialHighReturnedFinProductsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9SharedSumObservationsV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9NativeInputProductWitnessV1
open AspisR1S9PartialHighReturnedProductsV1
open AspisR1S9PartialHighReturnedFinProductsV1
open AspisR1S9NativeDecodedScalarProductV1
abbrev E := AspisWideTower.WideExact

def finIndex {n : Nat} (hn : n≤64) (i : Fin n) : Usize :=
  Usize.ofNatCore i.val (by have hi:=i.isLt; have hm:=Usize.cMax_bound; scalar_tac)
@[simp] theorem finIndex_val {n : Nat} (hn : n≤64) (i : Fin n) :
    (finIndex hn i).val=i.val := rfl

def fieldValue (f : Slice U8) (i : Usize) : E :=
  match weights.field f i with | .ok w => decodeNative w | _ => 0

def wideValue {N : Usize} (a : Array NativeW N) (i : Usize) : E :=
  match Array.index_usize a i with | .ok w => decodeNative w | _ => 0

def scalarValue {N : Usize} (a : Array NativeQ N) (i : Usize) : E :=
  match Array.index_usize a i with | .ok q => scalarEmbed q | _ => 0

/-- Direct finite source-observation equation. Every summand uses the SAME
actual field and common-array reads, not a free mathematical operand vector.
Invalid-read defaults are unreachable by the exported accepted read witnesses. -/
theorem partial_returned_source_sum
    (f : Slice U8) (common : Common) (s : Usize) (hs : s.val<4) (out : NativeW)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hrun : weights.partial_dot f common s=.ok (.Ok out)) :
    decodeNative out=∑ i : Fin 16,
      fieldValue f (AspisR1S9PartialDotReaderDomainV1.index s (finIndex (by decide) i))*
        scalarValue common (finIndex (by decide) i) := by
  obtain ⟨js,ps,final,hlen,hfinish,horder,hreads,hpositions,hvalue,hraw⟩ :=
    actual_partial_returned_fin16_product_sum f common s hs out hdiv hrun
  rw [hvalue]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨j,hj,hr⟩ := hpositions i
  have he : j=finIndex (by decide : 16≤64) i :=
    UScalar.eq_of_val_eq (hj.trans (finIndex_val (by decide) i).symm)
  subst j
  rcases hr with ⟨hf,hq⟩
  unfold fieldValue scalarValue
  rw [hf,hq]

/-- Same accepted shared-partials/high call; no independent operand values,
canonicality, finish or model success is supplied. -/
theorem high_returned_source_sum
    (f : Slice U8) (common : Common) (partials : Partials) (coeffs : Coeffs) (out : NativeW)
    (hproducer : weights.shared_partials f common=.ok (.Ok partials))
    (hrun : weights.high_dot partials coeffs=.ok (.Ok out)) :
    decodeNative out=∑ i : Fin 4,
      wideValue partials (finIndex (by decide) i)*scalarValue coeffs (finIndex (by decide) i) := by
  obtain ⟨js,ps,final,hlen,hfinish,horder,hreads,hpositions,hvalue,hraw⟩ :=
    actual_shared_high_returned_fin4_product_sum f common partials coeffs out hproducer hrun
  rw [hvalue]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨j,hj,hr⟩ := hpositions i
  have he : j=finIndex (by decide : 4≤64) i :=
    UScalar.eq_of_val_eq (hj.trans (finIndex_val (by decide) i).symm)
  subst j
  rcases hr with ⟨hw,hq⟩
  unfold wideValue scalarValue
  rw [hw,hq]

#print axioms finIndex_val
#print axioms partial_returned_source_sum
#print axioms high_returned_source_sum
end AspisR1S9SharedSumObservationsV1
