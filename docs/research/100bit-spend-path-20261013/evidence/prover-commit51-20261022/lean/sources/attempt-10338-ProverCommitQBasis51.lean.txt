import R1Z.ProverCommitTowerModel50
/-! Concrete M31 subfield and tower basis in the native QM31 value carrier. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitQBasis51
open AspisV8R15.ExactTowerBase
abbrev F := (algebraMap M31Exact QM31Exact).fieldRange

def i : QM31Exact := ⟨ProverCommitTower50.ci,0⟩
def u : QM31Exact := ⟨0,1⟩

theorem base_coordinates (a : M31Exact) :
    algebraMap M31Exact QM31Exact a=⟨⟨a,0⟩,0⟩ := by
  have he : algebraMap M31Exact QM31Exact=
      (algebraMap CM31Exact QM31Exact).comp (algebraMap M31Exact CM31Exact) := Subsingleton.elim _ _
  rw [he]
  rfl

def basis : R0P.PackBasis F := by
  refine ⟨i,u,?_⟩
  intro a b c d ha hb hc hd hs
  obtain ⟨a₀,rfl⟩ := RingHom.mem_fieldRange.mp ha
  obtain ⟨b₀,rfl⟩ := RingHom.mem_fieldRange.mp hb
  obtain ⟨c₀,rfl⟩ := RingHom.mem_fieldRange.mp hc
  obtain ⟨d₀,rfl⟩ := RingHom.mem_fieldRange.mp hd
  have h0 := congrArg (fun z : QM31Exact => z.re.re) hs
  have h1 := congrArg (fun z : QM31Exact => z.re.im) hs
  have h2 := congrArg (fun z : QM31Exact => z.im.re) hs
  have h3 := congrArg (fun z : QM31Exact => z.im.im) hs
  simp only [base_coordinates] at h0 h1 h2 h3
  dsimp [i,u,ProverCommitTower50.ci] at h0 h1 h2 h3
  simp only [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,zero_mul,mul_zero,zero_add,add_zero,one_mul,mul_one] at h0 h1 h2 h3
  simp [h0,h1,h2,h3]

theorem basis_i : basis.i=⟨ProverCommitTower50.ci,0⟩ := rfl
theorem basis_u : basis.u=⟨0,1⟩ := rfl

#print axioms base_coordinates
#print axioms basis
#print axioms basis_i
#print axioms basis_u
end R1Z.ProverCommitQBasis51
