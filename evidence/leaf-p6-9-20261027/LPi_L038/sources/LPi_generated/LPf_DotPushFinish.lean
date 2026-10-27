import LPf_DotPushCut
import LPf_DotFinish
import LPf_DotResidueStep
set_option autoImplicit false
namespace AspisR1.LPf_DotPushFinish
open Aeneas Aeneas.Std Result
abbrev Q := FIo_Native.fast_pairing.canonical.Q

theorem source (a b : Q) (s0 s1 s2 s3 r0 r1 r2 r3 : U64)
    (n : Nat) (hn : n < 4096)
    (h0 : s0.val ≤ n*LPf_DotWordStep.bound) (h1 : s1.val ≤ n*LPf_DotWordStep.bound)
    (h2 : s2.val ≤ n*LPf_DotWordStep.bound) (h3 : s3.val ≤ n*LPf_DotWordStep.bound)
    (rawCall : FIo_Native.fast_pairing.canonical.Q.raw a b =
      ok (Array.make 4#usize [r0,r1,r2,r3])) : ∃ z0 z1 z2 z3,
    (do let state ← FIo_Native.fast_pairing.canonical.Dot.push
          ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b
        FIo_Native.fast_pairing.canonical.Dot.finish state) =
      ok (Array.make 4#usize [z0,z1,z2,z3]) ∧
    z0.val = (s0.val+r0.val)%2147483647 ∧ z1.val = (s1.val+r1.val)%2147483647 ∧
    z2.val = (s2.val+r2.val)%2147483647 ∧ z3.val = (s3.val+r3.val)%2147483647 := by
  have push := LPf_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 rawCall
  obtain ⟨z0,z1,z2,z3,finish,v0,v1,v2,v3,_,_,_,_⟩ := LPf_DotFinish.source
    (LPf_DotPushFour.update s0 r0) (LPf_DotPushFour.update s1 r1)
    (LPf_DotPushFour.update s2 r2) (LPf_DotPushFour.update s3 r3)
  refine ⟨z0,z1,z2,z3,?_,?_,?_,?_,?_⟩
  · rw [push,bind_tc_ok,finish]
  · exact v0.trans (LPf_DotResidueStep.source s0 r0 n hn h0)
  · exact v1.trans (LPf_DotResidueStep.source s1 r1 n hn h1)
  · exact v2.trans (LPf_DotResidueStep.source s2 r2 n hn h2)
  · exact v3.trans (LPf_DotResidueStep.source s3 r3 n hn h3)

#print axioms source
end AspisR1.LPf_DotPushFinish
