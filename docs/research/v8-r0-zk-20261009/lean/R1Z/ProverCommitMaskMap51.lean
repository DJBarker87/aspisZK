import R0P.MaskValue
/-! Field-hom transport keeps the native QM31 result on the payload carrier. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitMaskMap51
open scoped BigOperators
variable {K L : Type} [Field K] [Field L] {F : Subfield K} {G : Subfield L}

theorem linear (f : K →+* L) (n : Nat) (a : Fin 10 → K) :
    f (R0P.Mask.maskLinear n a)=R0P.Mask.maskLinear n (fun i => f (a i)) := by
  simp only [R0P.Mask.maskLinear,map_sum,map_mul,map_natCast]

theorem basis (f : K →+* L) (B : R0P.PackBasis F) (C : R0P.PackBasis G)
    (hi : f B.i=C.i) (hu : f B.u=C.u) (j : Fin 4) :
    f (R0P.Mask.towerBasis B j)=R0P.Mask.towerBasis C j := by
  unfold R0P.Mask.towerBasis
  split_ifs <;> simp only [map_one,map_mul,hi,hu]

theorem multiply_basis (f : K →+* L) (B : R0P.PackBasis F) (C : R0P.PackBasis G)
    (hi : f B.i=C.i) (hu : f B.u=C.u) (x : K) (j : Fin 4) :
    f (R0P.Mask.mulTowerBasis B x j)=R0P.Mask.mulTowerBasis C (f x) j := by
  rw [R0P.Mask.mulTowerBasis,map_mul,basis f B C hi hu]
  rfl

theorem value (f : K →+* L) (B : R0P.PackBasis F) (C : R0P.PackBasis G)
    (hi : f B.i=C.i) (hu : f B.u=C.u)
    (c1 : Fin 16 → K) (mo : Fin 10 → K) (g : K) (a : Fin 10 → K) :
    f (R0P.Mask.maskValue B c1 mo g a)=R0P.Mask.maskValue C
      (fun i => f (c1 i)) (fun i => f (mo i)) (f g) (fun i => f (a i)) := by
  simp only [R0P.Mask.maskValue,R0P.Mask.maskFactors,map_add,map_sum,map_mul,
    multiply_basis f B C hi hu,map_pow,linear,map_one]

#print axioms linear
#print axioms basis
#print axioms multiply_basis
#print axioms value
end R1Z.ProverCommitMaskMap51
