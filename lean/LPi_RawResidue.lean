import LPi_RawValues
import LPf_DotFinish
set_option autoImplicit false
namespace AspisR1.LPi_RawResidue
open Aeneas Aeneas.Std Result

def residues (w : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (w.1%2147483647,w.2.1%2147483647,w.2.2.1%2147483647,w.2.2.2%2147483647)

theorem source (x y : LPi_RawValues.Q) (hx : LPi_RawValues.Canon x) (hy : LPi_RawValues.Canon y) :
    ∃ z0 z1 z2 z3 : U32,
      (do let raw ← FIo_Native.fast_pairing.canonical.Q.raw x y
          FIo_Native.fast_pairing.canonical.Dot.finish ⟨raw⟩) =
        ok (Array.make 4#usize [z0,z1,z2,z3]) ∧
      (z0.val,z1.val,z2.val,z3.val) = residues (LPi_RawValues.spec x y) ∧
      z0.val<2147483647 ∧ z1.val<2147483647 ∧ z2.val<2147483647 ∧ z3.val<2147483647 := by
  obtain ⟨r0,r1,r2,r3,raw,meaning⟩ := LPi_RawValues.source x y hx hy
  obtain ⟨z0,z1,z2,z3,finish,v0,v1,v2,v3,c0,c1,c2,c3⟩ := LPf_DotFinish.source r0 r1 r2 r3
  refine ⟨z0,z1,z2,z3,?_,?_,c0,c1,c2,c3⟩
  · rw [raw,bind_tc_ok,finish]
  · rw [v0,v1,v2,v3]
    exact congrArg residues meaning

#print axioms source
end AspisR1.LPi_RawResidue
