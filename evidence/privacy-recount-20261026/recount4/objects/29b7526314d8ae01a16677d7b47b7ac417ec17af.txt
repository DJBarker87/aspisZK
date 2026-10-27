import ExtractedCurrentQM31Exact
/-! Direct coordinate subtraction, independent of source-result transport. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSubDecode47
open AspisR1.ExtractedCurrentQM31Exact

theorem limb_sub (a b : Nat) (hb : b<AspisV8R15.ExactTowerBase.P) :
    (((a+AspisV8R15.ExactTowerBase.P-b)%AspisV8R15.ExactTowerBase.P : Nat) :
      AspisV8R15.ExactTowerBase.M31Exact) =
        (a : AspisV8R15.ExactTowerBase.M31Exact)-(b : AspisV8R15.ExactTowerBase.M31Exact) := by
  have hle : b≤a+AspisV8R15.ExactTowerBase.P := by omega
  rw [ZMod.natCast_mod,Nat.cast_sub hle,Nat.cast_add,ZMod.natCast_self,add_zero]

theorem coordinates (x y z : CurrentQM) (hy : CurrentCanonicalQM y)
    (ha : z.c0.a.val=(x.c0.a.val+2147483647-y.c0.a.val)%2147483647)
    (hb : z.c0.b.val=(x.c0.b.val+2147483647-y.c0.b.val)%2147483647)
    (hc : z.c1.a.val=(x.c1.a.val+2147483647-y.c1.a.val)%2147483647)
    (hd : z.c1.b.val=(x.c1.b.val+2147483647-y.c1.b.val)%2147483647) :
    decode z=decode x-decode y := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · change (z.c0.a.val : AspisV8R15.ExactTowerBase.M31Exact)=_
      rw [ha]
      exact limb_sub _ _ hy.1.1
    · change (z.c0.b.val : AspisV8R15.ExactTowerBase.M31Exact)=_
      rw [hb]
      exact limb_sub _ _ hy.1.2
  · apply QuadraticAlgebra.ext
    · change (z.c1.a.val : AspisV8R15.ExactTowerBase.M31Exact)=_
      rw [hc]
      exact limb_sub _ _ hy.2.1
    · change (z.c1.b.val : AspisV8R15.ExactTowerBase.M31Exact)=_
      rw [hd]
      exact limb_sub _ _ hy.2.2

#print axioms limb_sub
#print axioms coordinates
end R1Z.ProverCommitSubDecode47
