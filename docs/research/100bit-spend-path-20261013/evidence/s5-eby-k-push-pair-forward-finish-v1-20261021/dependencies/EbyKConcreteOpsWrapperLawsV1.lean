import AspisR1WeightsPairCutEbyKDotOpsV1
import EbyKConcreteOpsInstanceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5EbyKConcreteOpsWrapperLawsV1

open AspisR1WeightsPairCutEbyKDotOpsV1
open AspisR1S5EbyKConcreteOpsInstanceV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps := sourceOps

abbrev CutState := AspisR1WeightsPairCut.fast_pairing.EbyKDot
abbrev CutWide := AspisR1WeightsPairCut.field.WideExact
abbrev CutQm := AspisR1WeightsPairCut.field.QM31
abbrev SourceState := AspisR1EbyKPushDotBackend.PushState
abbrev SourceWide := AspisR1EbyKPushDotBackend.PushWide
abbrev SourceQm := AspisR1EbyKPushDotBackend.PushQm

def SourcePushUpdate (s out : SourceState) (value : SourceWide) (scalar : SourceQm) : Prop :=
  AspisR1EbyKPushDecodedProductUpdate.castSums out.c0.sums =
    AspisR1EbyKPushDecodedProductUpdate.tupleAdd
      (AspisR1EbyKPushDecodedProductUpdate.castSums s.c0.sums)
      (AspisR1.R22RawQmProductResidues.qmulCoefficients
        ((value.c0.c0.a.val,value.c0.c0.b.val),(value.c0.c1.a.val,value.c0.c1.b.val))
        ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val))) ∧
  AspisR1EbyKPushDecodedProductUpdate.castSums out.c1.sums =
    AspisR1EbyKPushDecodedProductUpdate.tupleAdd
      (AspisR1EbyKPushDecodedProductUpdate.castSums s.c1.sums)
      (AspisR1.R22RawQmProductResidues.qmulCoefficients
        ((value.c1.c0.a.val,value.c1.c0.b.val),(value.c1.c1.a.val,value.c1.c1.b.val))
        ((scalar.c0.a.val,scalar.c0.b.val),(scalar.c1.a.val,scalar.c1.b.val)))

/-- A successful class-level operation is the same successful source-state
transition installed by `sourceOps`, followed by the explicit carrier map
back to the Pair cut's nominal state. -/
theorem installed_push_success_map
    (s : CutState) (value : CutWide) (scalar : CutQm)
    (status : core.result.Result Unit Unit) (out : CutState)
    (h : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push s value scalar =
      .ok (status, out)) :
    ∃ sourceOut : SourceState,
      sourceOps.push (stateToSource s) (wideToSource value) (qToSource scalar) =
        .ok (status, sourceOut) ∧ stateFromSource sourceOut = out := by
  have hsource : ∃ sourceOut,
      AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushDecodedProductUpdate.QRaw
        (stateToSource s) (wideToSource value) (qToSource scalar) =
          .ok (status, sourceOut) ∧ stateFromSource sourceOut = out := by
    simpa [AspisR1WeightsPairCut.fast_pairing.EbyKDot.push] using h
  rcases hsource with ⟨sourceOut, hrun, hmap⟩
  exact ⟨sourceOut, by simpa [sourceOps] using hrun, hmap⟩

/-- The typed wrapper inherits the concrete QRaw product update. The premise
names the mapped source accumulator bounds and input canonicality explicitly,
so this theorem does not silently transfer a carrier invariant. -/
theorem installed_push_product_update
    (s : CutState) (value : CutWide) (scalar : CutQm)
    (out : CutState)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
      (wideToSource value))
    (hacc0 : ∀ x ∈ (stateToSource s).c0.sums.val, x.val < 2^46)
    (hacc1 : ∀ x ∈ (stateToSource s).c1.sums.val, x.val < 2^46)
    (hrun : AspisR1WeightsPairCut.fast_pairing.EbyKDot.push s value scalar =
      .ok (.Ok (), out)) :
    ∃ sourceOut : SourceState,
      stateFromSource sourceOut = out ∧
      SourcePushUpdate (stateToSource s) sourceOut (wideToSource value)
        (qToSource scalar) := by
  obtain ⟨sourceOut, hsource, hmap⟩ :=
    installed_push_success_map s value scalar (.Ok ()) out hrun
  have hupdate := concrete_push_product_update
    (stateToSource s) (wideToSource value) (qToSource scalar) sourceOut
    hcanonical hacc0 hacc1 hsource
  exact ⟨sourceOut, hmap, by simpa [SourcePushUpdate] using hupdate⟩

#print axioms installed_push_success_map
#print axioms installed_push_product_update
end AspisR1S5EbyKConcreteOpsWrapperLawsV1
