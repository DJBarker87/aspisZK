import S9RegularKindExecutionV1
import S9RegularReturnedFinProductsV1
import S9RegularReadRawDomainV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open scoped BigOperators
namespace AspisR1S9RegularKindReturnedFinProductsV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9RegularKindExecutionV1
open AspisR1S9RegularReturnedFinProductsV1
open AspisR1S9NativeInputProductWitnessV1
open AspisR1S9NativeDecodedScalarProductV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- SAME accepted S2/twofold inlined process_kind, with its complete tensor,
borrow-back, scale, actual zero/push/finish and stored-write execution retained.
Its actual dot value is the ordinary ordered sum over the SAME source reads.
The count is actual division output, not an assumed scratch or tensor length. -/
theorem actual_process_kind_returned_fin_products
    (self : weights.Weights) (kind : Usize) (alpha : Slice W) (f : Slice U8)
    (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok n)
    (hcall : weights.process_kind self kind alpha f 2#usize n ap0 ap1 scratch parts=
      .ok (.Ok (),scratchOut,partsOut)) :
    ∃ (e : Execution self kind f n ap0 ap1 scratch scratchOut parts partsOut)
      (js : List Usize) (ps : List NativePair) (hlen : ps.length=n.val),
      js.map (fun j => j.val)=List.range' 0 n.val ∧
      List.Forall₂ (actualReads f (alloc.vec.Vec.deref scratchOut)) js ps ∧
      (∀ i : Fin n.val, ∃ j : Usize, j.val=i.val ∧
        actualReads f (alloc.vec.Vec.deref scratchOut) j (ps.get (Fin.cast hlen.symm i))) ∧
      decodeNative (Execution.dotValue e)=(∑ i : Fin n.val,
        decodeNative (ps.get (Fin.cast hlen.symm i)).1 *
          scalarEmbed (ps.get (Fin.cast hlen.symm i)).2) ∧
      (∀ i : Fin n.val, ∀ dot scalar,
        AspisR1S9ActualRawEbyKBodyV1.pushWithRaw
          AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw
          dot (ps.get (Fin.cast hlen.symm i)).1 scalar =
        fast_pairing.EbyKDot.push dot (ps.get (Fin.cast hlen.symm i)).1 scalar) := by
  obtain ⟨e⟩ := process_kind_success_execution self kind alpha f n ap0 ap1
    scratch scratchOut parts partsOut hs2 hcall
  obtain ⟨js,ps,hlen,horder,hreads,hpositions,hvalue⟩ :=
    actual_new_push_finish_returned_fin_product_sum f (alloc.vec.Vec.deref scratchOut)
      n (Execution.initialDot e) (Execution.finalDot e) (Execution.dotValue e) (Execution.newDot e) hdiv (Execution.pushes e) (Execution.finish e)
  refine ⟨e,js,ps,hlen,horder,hreads,hpositions,hvalue,?_⟩
  intro i dot scalar
  obtain ⟨j,hj,hread⟩ := hpositions i
  have hjlt : j.val<n.val := by rw [hj];exact i.isLt
  exact AspisR1S9RegularReadRawDomainV1.regular_read_actual_raw_source_eq
    f n j hjlt hdiv (ps.get (Fin.cast hlen.symm i)).1 hread.1 dot scalar

#print axioms actual_process_kind_returned_fin_products
end AspisR1S9RegularKindReturnedFinProductsV1
