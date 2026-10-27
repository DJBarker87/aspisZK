import LPi_RawValues
import LPf_DotPushFinish
set_option autoImplicit false
namespace AspisR1.LPi_DotAssociation
open Aeneas Aeneas.Std Result
abbrev Q := FIo_Native.fast_pairing.canonical.Q

/-- LPf's same-state push/finish theorem with its opaque raw-call observation
removed. Canonical inputs are the checked Q constructor domain. -/
theorem source (a b : Q) (ha : LPi_RawValues.Canon a) (hb : LPi_RawValues.Canon b)
    (s0 s1 s2 s3 : U64) (n : Nat) (hn : n < 4096)
    (h0 : s0.val ≤ n*LPf_DotWordStep.bound) (h1 : s1.val ≤ n*LPf_DotWordStep.bound)
    (h2 : s2.val ≤ n*LPf_DotWordStep.bound) (h3 : s3.val ≤ n*LPf_DotWordStep.bound) :
    ∃ (r0 r1 r2 r3 : U64) (z0 z1 z2 z3 : U32),
      (r0.val,r1.val,r2.val,r3.val) = LPi_RawValues.spec a b ∧
      (do let state ← FIo_Native.fast_pairing.canonical.Dot.push
            ⟨Array.make 4#usize [s0,s1,s2,s3]⟩ a b
          FIo_Native.fast_pairing.canonical.Dot.finish state) =
        ok (Array.make 4#usize [z0,z1,z2,z3]) ∧
      z0.val = (s0.val+r0.val)%2147483647 ∧ z1.val = (s1.val+r1.val)%2147483647 ∧
      z2.val = (s2.val+r2.val)%2147483647 ∧ z3.val = (s3.val+r3.val)%2147483647 := by
  obtain ⟨r0,r1,r2,r3,raw,meaning⟩ := LPi_RawValues.source a b ha hb
  obtain ⟨z0,z1,z2,z3,run,v0,v1,v2,v3⟩ :=
    LPf_DotPushFinish.source a b s0 s1 s2 s3 r0 r1 r2 r3 n hn h0 h1 h2 h3 raw
  exact ⟨r0,r1,r2,r3,z0,z1,z2,z3,meaning,run,v0,v1,v2,v3⟩

#print axioms source
end AspisR1.LPi_DotAssociation
