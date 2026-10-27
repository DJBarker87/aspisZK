import LPf_DotPushFour
set_option autoImplicit false
namespace AspisR1.LPf_DotPushCut
open Aeneas Aeneas.Std Result
abbrev Q := FIo_Native.fast_pairing.canonical.Q

/-- Source-order join of the actual raw call with the complete four-cell
update loop. The one unproved raw-call boundary remains explicit. -/
theorem source (a b : Q) (s0 s1 s2 s3 r0 r1 r2 r3 : U64)
    (rawCall : FIo_Native.fast_pairing.canonical.Q.raw a b =
      ok (Array.make 4#usize [r0,r1,r2,r3])) :
    FIo_Native.fast_pairing.canonical.Dot.push
      ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b =
      ok ⟨Array.make 4#usize [LPf_DotPushFour.update s0 r0,LPf_DotPushFour.update s1 r1,
        LPf_DotPushFour.update s2 r2,LPf_DotPushFour.update s3 r3]⟩ := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push
  rw [rawCall,bind_tc_ok]
  exact LPf_DotPushFour.source s0 s1 s2 s3 r0 r1 r2 r3

#print axioms source
end AspisR1.LPf_DotPushCut
