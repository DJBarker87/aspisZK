import AspisR1WeightsPairCutEbyKDotOpsV1
import FourDotsTailAcceptedTraceRootV1
import S4TailFinishSourceMapV1
import S5QRaw.EbyKPushDecodedProductUpdateV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5EbyKConcreteOpsInstanceV1

abbrev Tail := AspisR1FastDotsActualCallbackTailTraceRootV1.Tail
abbrev PushState := AspisR1EbyKPushDotBackend.PushState
abbrev PushWide := AspisR1EbyKPushDotBackend.PushWide
abbrev PushQm := AspisR1EbyKPushDotBackend.PushQm

/-- Concrete source-model operations installed in D18's typed EbyK carrier.
The S4 constructor and finish are the retained PushCutV3 implementations;
push is the exact QRaw generated Dot backend used by the S5 product proof. -/
@[reducible] def sourceOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps where
  new := AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource
  push := fun s value scalar => AspisR1EbyKPushDotBackend.pushWithDotBackend
    AspisR1EbyKPushDecodedProductUpdate.QRaw s value scalar
  finish := AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent

@[simp] theorem sourceOps_new_zero : sourceOps.new = .ok
    EbyKNewToPushStateABI.pushZero :=
  AspisR1FastDotsTailAcceptedTraceRootV1.newFromSource_zero

@[simp] theorem sourceOps_push_eq (s : Tail) (value : PushWide) (scalar : PushQm) :
    sourceOps.push s value scalar =
      AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushDecodedProductUpdate.QRaw s value scalar := rfl

@[simp] theorem sourceOps_finish_eq (s : Tail) :
    sourceOps.finish s = AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent s := rfl

/-- Successful concrete ops preserve the exact two-lane modular Q product
update. Canonicality and the pre-call `<2^46` accumulator bounds are explicit
at the one-call interface. -/
theorem concrete_push_product_update
    (s : PushState) (value : PushWide) (scalar : PushQm) (out : PushState)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical value)
    (hacc0 : ∀ x ∈ s.c0.sums.val, x.val < 2^46)
    (hacc1 : ∀ x ∈ s.c1.sums.val, x.val < 2^46)
    (hrun : sourceOps.push s value scalar = .ok (.Ok (),out)) :
    AspisR1EbyKPushDecodedProductUpdate.castSums out.c0.sums =
      AspisR1EbyKPushDecodedProductUpdate.tupleAdd
        (AspisR1EbyKPushDecodedProductUpdate.castSums s.c0.sums)
        (AspisR1.R22RawQmProductResidues.qmulCoefficients
          ((value.c0.c0.a.val,value.c0.c0.b.val),
           (value.c0.c1.a.val,value.c0.c1.b.val))
          ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))) ∧
    AspisR1EbyKPushDecodedProductUpdate.castSums out.c1.sums =
      AspisR1EbyKPushDecodedProductUpdate.tupleAdd
        (AspisR1EbyKPushDecodedProductUpdate.castSums s.c1.sums)
        (AspisR1.R22RawQmProductResidues.qmulCoefficients
          ((value.c1.c0.a.val,value.c1.c0.b.val),
           (value.c1.c1.a.val,value.c1.c1.b.val))
          ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))) := by
  apply AspisR1EbyKPushDecodedProductUpdate.successful_push_decoded_product_update
    s value scalar out hcanonical hacc0 hacc1
  simpa [sourceOps] using hrun

/-- Successful installed push exposes both QRaw calls, both exact accumulator
writes, the source count guard and the numeric increment. -/
theorem concrete_push_source_contract
    (s : PushState) (value : PushWide) (scalar : PushQm) (out : PushState)
    (hrun : sourceOps.push s value scalar = .ok (.Ok (),out)) :
    ∃ lo hi : Array U64 4#usize,
      AspisR1EbyKPushDecodedProductUpdate.QRaw
        (AspisR1EbyKPushDotBackend.valueLo value)
        (AspisR1EbyKPushDotBackend.scalarQ scalar) = .ok lo ∧
      AspisR1EbyKPushDecodedProductUpdate.QRaw
        (AspisR1EbyKPushDotBackend.valueHi value)
        (AspisR1EbyKPushDotBackend.scalarQ scalar) = .ok hi ∧
      out.c0.sums = AspisR1DotPushLocal.Proof.updatedSums s.c0.sums lo ∧
      out.c1.sums = AspisR1DotPushLocal.Proof.updatedSums s.c1.sums hi ∧
      s.count < AspisR1EbyKPushExplicitOpsV1.maxTerms ∧
      out.count.val = s.count.val + 1 ∧
      (∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ scalar).val,
        x.val < 2147483647) := by
  apply AspisR1EbyKPushDotBackend.successful_push_exact_backend
  simpa [sourceOps] using hrun

/-- The installed finish is total and its eight returned words are exactly the
source reducer's residues of the current accumulator cells. -/
theorem concrete_finish_residues (s : Tail) :
    ∃ out : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact,
      sourceOps.finish s = .ok out ∧
      (AspisR1FastDotsTailFinishSourceMapV1.currentFinishWords out).map
        (fun w => w.val) =
        ((s.c0.sums.val ++ s.c1.sums.val).map
          (fun x => x.val % AspisV8R17.RawReducer.P)) := by
  simpa [sourceOps] using
    AspisR1FastDotsTailFinishSourceMapV1.finishTailCurrent_total_residue_values s

#print axioms sourceOps_new_zero
#print axioms sourceOps_push_eq
#print axioms sourceOps_finish_eq
#print axioms concrete_push_product_update
#print axioms concrete_push_source_contract
#print axioms concrete_finish_residues
end AspisR1S5EbyKConcreteOpsInstanceV1
