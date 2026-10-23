import S9RegularKindExecutionV1
import S9ActualRegularKindsTraceV1
import S9FactorArrayEntryV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9RegularCell4FrameV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9RegularKindExecutionV1
open AspisR1S9ActualRegularKindsTraceV1
open AspisR1S9FactorArrayEntryV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- Exact accepted regular kind writes its own kind, so preserves incoming
slot4 for the actual admitted regular kinds. No field/Can/value premises. -/
theorem kind_success_cell4_frame
    (self : weights.Weights) (kind : Usize) (alpha : Slice W) (f : Slice U8) (n : Usize)
    (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2) (hk : kind.val<7) (hne : kind.val≠4)
    (hcall : weights.process_kind self kind alpha f 2#usize n ap0 ap1 scratch parts=
      .ok (.Ok (),scratchOut,partsOut)) :
    atN partsOut 4#usize (by decide)=atN parts 4#usize (by decide) := by
  obtain ⟨e⟩ := process_kind_success_execution self kind alpha f n ap0 ap1
    scratch scratchOut parts partsOut hs2 hcall
  have he := accepted_update_eq_set parts kind hk (Execution.storedValue e) partsOut (Execution.write e)
  have hn : (4#usize).val≠kind.val := by change 4≠kind.val;omega
  rw [he,atN_set parts kind 4#usize (Execution.storedValue e) hk (by decide),if_neg hn]

/-- The actual shared/unshared regular driver writes only literal kinds
2/5/6 or1/2/3/5/6. Thus its SAME incoming part4 is preserved, including zero
from the caller's initialization, with no scalar/arithmetic assumptions. -/
theorem actual_regular_success_cell4_frame
    (self : weights.Weights) (shared : Bool) (alpha : Slice W) (f : Slice U8) (n : Usize)
    (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2)
    (hcall : weights.process_regular_kinds self shared alpha f 2#usize n ap0 ap1 scratch parts=
      .ok (.Ok (),scratchOut,partsOut)) :
    atN partsOut 4#usize (by decide)=atN parts 4#usize (by decide) := by
  have ht := regular_success_trace self shared alpha f 2#usize n ap0 ap1
    scratch scratchOut parts partsOut hcall
  cases shared with
  | true =>
    simp only [RegularTrace,↓reduceIte] at ht
    obtain ⟨s1,s2,p1,p2,h1,h2,h3⟩ := ht
    have a := kind_success_cell4_frame self 2#usize alpha f n ap0 ap1 scratch s1 parts p1
      hs2 (by decide) (by decide) h1
    have b := kind_success_cell4_frame self 5#usize alpha f n ap0 ap1 s1 s2 p1 p2
      hs2 (by decide) (by decide) h2
    have c := kind_success_cell4_frame self 6#usize alpha f n ap0 ap1 s2 scratchOut p2 partsOut
      hs2 (by decide) (by decide) h3
    exact c.trans (b.trans a)
  | false =>
    simp only [RegularTrace,Bool.false_eq_true,↓reduceIte] at ht
    obtain ⟨s1,s2,s3,s4,p1,p2,p3,p4,h1,h2,h3,h4,h5⟩ := ht
    have a := kind_success_cell4_frame self 1#usize alpha f n ap0 ap1 scratch s1 parts p1
      hs2 (by decide) (by decide) h1
    have b := kind_success_cell4_frame self 2#usize alpha f n ap0 ap1 s1 s2 p1 p2
      hs2 (by decide) (by decide) h2
    have c := kind_success_cell4_frame self 3#usize alpha f n ap0 ap1 s2 s3 p2 p3
      hs2 (by decide) (by decide) h3
    have d := kind_success_cell4_frame self 5#usize alpha f n ap0 ap1 s3 s4 p3 p4
      hs2 (by decide) (by decide) h4
    have e := kind_success_cell4_frame self 6#usize alpha f n ap0 ap1 s4 scratchOut p4 partsOut
      hs2 (by decide) (by decide) h5
    exact e.trans (d.trans (c.trans (b.trans a)))

#print axioms kind_success_cell4_frame
#print axioms actual_regular_success_cell4_frame
end AspisR1S9RegularCell4FrameV1
