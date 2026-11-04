import NEV_QRawAssociation
import LPf_DotPushCut
import LPi_DotPushTotal
set_option autoImplicit false
noncomputable section
namespace NEV_DotPush
open Aeneas Aeneas.Std Result AspisR1
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Q := FIo_Native.fast_pairing.canonical.Q
/-- Actual raw forest followed by the retained literal native four-cell loop.
The native arbitrary-prestate iteration is K050/K051, not a whole-buffer proof. -/
def cut (self : Dot) (a b : Q) : Result Dot := do
 let raw ← NEV_QRaw.fast_pairing.canonical.Q.raw a b
 FIo_Native.fast_pairing.canonical.Dot.push_loop
   {start:=0#usize,«end»:=4#usize} self raw

theorem association (self : Dot) (a b : Q) :
    cut self a b=FIo_Native.fast_pairing.canonical.Dot.push self a b := by
  unfold cut FIo_Native.fast_pairing.canonical.Dot.push
  rw [NEV_QRawAssociation.actual]

/-- Complete four-word output, exact SAME raw call and its natural-word spec.
The existing finite-loop induction and raw arithmetic are reused unchanged. -/
theorem complete (a b : Q) (ha : LPi_RawValues.Canon a) (hb : LPi_RawValues.Canon b)
    (s0 s1 s2 s3 : U64) : ∃ r0 r1 r2 r3 : U64,
    (r0.val,r1.val,r2.val,r3.val)=LPi_RawValues.spec a b ∧
    cut ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b=
      ok ⟨Array.make 4#usize [LPf_DotPushFour.update s0 r0,LPf_DotPushFour.update s1 r1,
        LPf_DotPushFour.update s2 r2,LPf_DotPushFour.update s3 r3]⟩ := by
  obtain ⟨r0,r1,r2,r3,raw,values⟩ := LPi_RawValues.source a b ha hb
  exact ⟨r0,r1,r2,r3,values,(association _ a b).trans
    (LPf_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 raw)⟩
#print axioms association
#print axioms complete
end NEV_DotPush
end
