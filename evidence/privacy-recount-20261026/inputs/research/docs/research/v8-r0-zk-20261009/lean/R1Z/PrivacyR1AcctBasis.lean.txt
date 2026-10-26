import R1Z.PrivacyR1Headline
import R1Z.ProverCommitSourceCounts

set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1AcctBasis
open AspisWideTower AspisV8R15.ExactTowerBase
abbrev K := WideExact
abbrev F := ProverCommitWordCarrier.sourceBase (K := K)
def i : K := ⟨⟨⟨0, 1⟩, 0⟩, 0⟩
def u : K := ⟨⟨0, 1⟩, 0⟩

theorem base_coordinates (a : ZMod AspisCircleGroupOrder.P) :
    algebraMap (ZMod AspisCircleGroupOrder.P) K a = ⟨⟨⟨a, 0⟩, 0⟩, 0⟩ := by
  have he : algebraMap (ZMod AspisCircleGroupOrder.P) K =
      (algebraMap QM31Exact K).comp ((algebraMap CM31Exact QM31Exact).comp
        (algebraMap M31Exact CM31Exact)) := Subsingleton.elim _ _
  rw [he]
  rfl

def basis : R0P.PackBasis F := by
  refine ⟨i, u, ?_⟩
  intro a b c d ha hb hc hd hs
  obtain ⟨a₀, rfl⟩ := RingHom.mem_fieldRange.mp ha
  obtain ⟨b₀, rfl⟩ := RingHom.mem_fieldRange.mp hb
  obtain ⟨c₀, rfl⟩ := RingHom.mem_fieldRange.mp hc
  obtain ⟨d₀, rfl⟩ := RingHom.mem_fieldRange.mp hd
  have h0 := congrArg (fun z : K => z.re.re.re) hs
  have h1 := congrArg (fun z : K => z.re.re.im) hs
  have h2 := congrArg (fun z : K => z.re.im.re) hs
  have h3 := congrArg (fun z : K => z.re.im.im) hs
  simp only [base_coordinates] at h0 h1 h2 h3
  dsimp [i, u] at h0 h1 h2 h3
  simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one] at h0 h1 h2 h3
  simp [h0, h1, h2, h3]

theorem i_sq : basis.i * basis.i = -1 := by
  change i * i = -1
  have hi : i = algebraMap QM31Exact K (algebraMap CM31Exact QM31Exact cm31I) := rfl
  rw [hi, ← map_mul, ← map_mul, cm31I_mul_self, map_neg, map_one, map_neg, map_one]

theorem u_sq : basis.u * basis.u = 2 + basis.i := by
  change u * u = 2 + i
  change (⟨⟨0, 1⟩, 0⟩ : K) * ⟨⟨0, 1⟩, 0⟩ = 2 + ⟨⟨⟨0, 1⟩, 0⟩, 0⟩
  norm_num [QuadraticAlgebra.mk_mul_mk, qm31R]
  rfl

theorem packing_laws : R0Z.K4.PackField basis := by
  constructor
  · rw [i_sq]; exact F.neg_mem F.one_mem
  · exact ⟨2, 1, (by simpa only [one_add_one_eq_two] using F.add_mem F.one_mem F.one_mem), F.one_mem, by simpa only [mul_one] using u_sq⟩

#print axioms base_coordinates
#print axioms basis
#print axioms i_sq
#print axioms u_sq
#print axioms packing_laws
end R1Z.PrivacyR1AcctBasis
