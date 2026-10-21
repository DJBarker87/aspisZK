import EbyKPushDotBackend
import AspisR1EbyKDotPushSourceV1.LoopAdapter
import OriginalDotPushRawLoopToLiteralV1
import DotPushSourceResidues
import DotPushSuccessResidues
import S4ConcreteTailInstalledThreePushesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S4DotPushCallEqualityV1

abbrev PushDot := AspisR1EbyKPushDotBackend.PushDot
abbrev PushQ := AspisR1EbyKPushDotBackend.PushQ
abbrev RawFn := AspisR1EbyKPushDotBackend.RawFn
abbrev SourceDot := AspisR1EbyKDotPushSourceV1.fast_pairing.canonical.Dot
abbrev SourceQ := AspisR1EbyKDotPushSourceV1.fast_pairing.canonical.Q

/-- The source adapter's generated `Dot.push_raw` result mapped into the
    explicit PairCut Dot carrier. -/
def sourceDotPush (rawFn : RawFn) (self : PushDot) (a b : PushQ) : Result PushDot :=
  do
    let out ← AspisR1EbyKDotPushSourceV1.fast_pairing.canonical.Dot.push_raw rawFn
      (⟨self.sums⟩ : SourceDot) (a : SourceQ) (b : SourceQ)
    .ok (⟨out.sums⟩ : PushDot)

/-- Exact full-result equality for local Dot.push versus the retained generated source
    `Dot.push_raw`, after mapping only the one-field Dot carrier. -/
theorem dot_via_raw_eq_generated_push_raw (rawFn : RawFn) (self : PushDot)
    (a b : PushQ) :
    AspisR1EbyKPushDotBackend.dotViaRaw rawFn self a b = sourceDotPush rawFn self a b := by
  unfold AspisR1EbyKPushDotBackend.dotViaRaw sourceDotPush
    AspisR1EbyKDotPushSourceV1.fast_pairing.canonical.Dot.push_raw
  cases hraw : rawFn a b with
  | fail e => simp only [AspisR1DotPushLocal.canonical.Dot.push, hraw, bind_tc_fail]
  | div => simp only [AspisR1DotPushLocal.canonical.Dot.push, hraw, bind_tc_div]
  | ok raw =>
      have hlocal : AspisR1DotPushLocal.canonical.Dot.push rawFn
          (⟨self.sums⟩ : AspisR1DotPushLocal.canonical.Dot) a b =
          .ok ⟨AspisR1DotPushLocal.Proof.updatedSums self.sums raw⟩ :=
        AspisR1DotPushLocal.Proof.push_total_from_raw rawFn ⟨self.sums⟩ a b raw hraw
      have hsrc : AspisR1EbyKDotPushSourceV1.fast_pairing.canonical.Dot.push_loop
          { start := 0#usize, «end» := 4#usize } (⟨self.sums⟩ : SourceDot) raw =
          .ok ⟨AspisR1DotPushLocal.Proof.updatedSums self.sums raw⟩ := by
        obtain ⟨a0,a1,a2,a3,hs⟩ := List.length_eq_four.mp self.sums.property
        obtain ⟨r0,r1,r2,r3,hr⟩ := List.length_eq_four.mp raw.property
        have hs' : self.sums = Array.make 4#usize [a0,a1,a2,a3] := Subtype.ext hs
        have hr' : raw = Array.make 4#usize [r0,r1,r2,r3] := Subtype.ext hr
        have hgen := AspisR1DotPushOriginalRaw.Proof.loop_eq_updatedSums a0 a1 a2 a3 r0 r1 r2 r3
        rw [← hs', ← hr'] at hgen
        exact hgen
      simp only [hraw, bind_tc_ok, hlocal, hsrc]

/-- The installed QRaw push is the explicit emitted push body with its Dot child
    specialized to the retained generated Dot loop adapter. -/
theorem qraw_backend_eq_generated_dot_control
    (self : AspisR1EbyKPushDotBackend.PushState)
    (value : AspisR1EbyKPushDotBackend.PushWide)
    (scalar : AspisR1EbyKPushDotBackend.PushQm) :
    AspisR1EbyKPushDotBackend.pushWithDotBackend
        AspisR1EbyKPushDecodedProductUpdate.QRaw self value scalar =
      AspisR1EbyKPushExplicitOpsV1.pushWithOps
        AspisR1EbyKPushWideToQ.fromWide
        AspisR1FastDotsConcreteTailInstalledThreePushesV1.ConcreteCheckedQ
        (sourceDotPush AspisR1EbyKPushDecodedProductUpdate.QRaw)
        UScalar.add self value scalar := by
  have hdot :
      AspisR1FastDotsConcreteTailInstalledThreePushesV1.ConcreteDotPush =
        sourceDotPush AspisR1EbyKPushDecodedProductUpdate.QRaw := by
    funext d a b
    exact dot_via_raw_eq_generated_push_raw
      AspisR1EbyKPushDecodedProductUpdate.QRaw d a b
  rw [AspisR1FastDotsConcreteTailInstalledThreePushesV1.qraw_backend_eq_explicit_source_control]
  rw [hdot]

#print axioms dot_via_raw_eq_generated_push_raw
#print axioms qraw_backend_eq_generated_dot_control
end AspisR1S4DotPushCallEqualityV1
