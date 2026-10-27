import LPn_DotJoin
import LPn_DotPushFour
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPn.DotState

def project (s : FIo_Native.fast_pairing.canonical.Dot) : fast_pairing.canonical.Dot := ⟨s.sums⟩

theorem update_eq (before raw : U64) :
    AspisR1.LPn_DotPushFour.update before raw =
      LPn_Kit_u64 (before.val + LPn_Kit_partial raw.val) := by
  apply UScalar.eq_of_val_eq
  change (U64.wrapping_add before (AspisR1.FIo_ReduceBounds.fold raw)).val =
    (before.val+LPn_Kit_partial raw.val)%18446744073709551616
  rw [U64.wrapping_add_val_eq,AspisR1.LPn.Raw.size64,AspisR1.LPn.Raw.partial_nat]
  rfl

/-- Keep raw representatives as variables. In particular no concrete raw
    product expressions are reduced while checking this state/Result port. -/
theorem model (a b : fast_pairing.canonical.Q) (s0 s1 s2 s3 r0 r1 r2 r3 : U64)
    (words : LPn_Kit_raw a b=[r0.val,r1.val,r2.val,r3.val]) :
    fast_pairing.canonical.Dot.push ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b =
      ok ⟨Array.make 4#usize [AspisR1.LPn_DotPushFour.update s0 r0,
        AspisR1.LPn_DotPushFour.update s1 r1,AspisR1.LPn_DotPushFour.update s2 r2,
        AspisR1.LPn_DotPushFour.update s3 r3]⟩ := by
  unfold fast_pairing.canonical.Dot.push
  rw [words]
  change ok (⟨Array.make 4#usize
    [LPn_Kit_u64 (s0.val+LPn_Kit_partial r0.val),
     LPn_Kit_u64 (s1.val+LPn_Kit_partial r1.val),
     LPn_Kit_u64 (s2.val+LPn_Kit_partial r2.val),
     LPn_Kit_u64 (s3.val+LPn_Kit_partial r3.val)]⟩ : fast_pairing.canonical.Dot) = _
  simp only [update_eq]

theorem source (a b : FIo_Native.fast_pairing.canonical.Q)
    (s0 s1 s2 s3 r0 r1 r2 r3 : U64)
    (call : FIo_Native.fast_pairing.canonical.Q.raw a b = ok (Array.make 4#usize [r0,r1,r2,r3]))
    (words : LPn_Kit_raw a b=[r0.val,r1.val,r2.val,r3.val]) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.push ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b=ok out ∧
      fast_pairing.canonical.Dot.push ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b=ok (project out) := by
  exact ⟨_,AspisR1.LPn_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 call,
    model a b s0 s1 s2 s3 r0 r1 r2 r3 words⟩

#print axioms update_eq
#print axioms model
#print axioms source
end LPn.DotState
