import CompPolyFactorRecursion

noncomputable section
namespace AspisR1.CompPolyFactorCertificate
open CompPoly Polynomial AspisR1.CompPolyFactorRecursion
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def linearProduct (roots : List K) : K[X] :=
  (roots.map (fun a => (X - C a : K[X]))).prod

theorem linearProduct_root_iff (roots : List K) (x : K) :
    IsRoot (linearProduct roots) x ↔ x ∈ roots := by
  induction roots with
  | nil => simp [linearProduct, IsRoot]
  | cons a roots ih =>
    change IsRoot ((X-C a) * linearProduct roots) x ↔ x ∈ a::roots
    simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero,
      sub_eq_zero, List.mem_cons]
    exact or_congr Iff.rfl ih

theorem linearProduct_monic_degree (roots : List K) :
    (linearProduct roots).Monic ∧ (linearProduct roots).natDegree = roots.length := by
  induction roots with
  | nil => simp [linearProduct]
  | cons a roots ih =>
    change ((X-C a) * linearProduct roots).Monic ∧
      ((X-C a) * linearProduct roots).natDegree = (a::roots).length
    refine ⟨(monic_X_sub_C a).mul ih.1, ?_⟩
    rw [natDegree_mul (monic_X_sub_C a).ne_zero ih.1.ne_zero,
      natDegree_X_sub_C, ih.2, List.length_cons]
    omega

theorem factor_complete (q t : Nat) (coins : Nat → Fin t → K × K)
    (fuel node : Nat) (f : CPolynomial K) (roots : List K)
    (hf : f.toPoly.Monic) (hs : factor q t coins fuel node f = some roots) :
    (∀ x, IsRoot f.toPoly x ↔ x ∈ roots) ∧ roots.length = f.toPoly.natDegree := by
  have hp : linearProduct roots = f.toPoly := factor_product q t coins fuel node f roots hf hs
  constructor
  · intro x
    rw [← hp]
    exact linearProduct_root_iff roots x
  · rw [← hp]
    exact (linearProduct_monic_degree roots).2.symm

#print axioms linearProduct_root_iff
#print axioms linearProduct_monic_degree
#print axioms factor_complete
end AspisR1.CompPolyFactorCertificate
