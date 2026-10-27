import WAdm_WideIndices
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_WideCarrier
open OraclePortCkptAbi2Extracted OraclePortCkptAbi4Decode
abbrev E := aspis_core.field.wide_exact.WideExact

abbrev limbs := WAdm_WideIndices.limbs

attribute [local irreducible] aspis_core.field.wide_exact.WideExact.from_limbs

/-- Every canonical raw carrier is exactly a legal private WideExact
constructor result, rather than an invented value outside the Rust domain. -/
theorem from_limbs (q : E) (canonical : CanonicalWide q) :
    aspis_core.field.wide_exact.WideExact.from_limbs (limbs q) = ok (some q) := by
  rcases canonical with ⟨⟨h0,h1,h2,h3⟩,⟨h4,h5,h6,h7⟩⟩
  have below (x : U32) (h : x.val < 2147483647) : ¬ x ≥ aspis_core.field.P := by
    rw [aspis_core.field.P]
    change ¬ (2147483647#u32 : U32).val ≤ x.val
    exact Nat.not_le.mpr h
  have n0 := below _ h0
  have n1 := below _ h1
  have n2 := below _ h2
  have n3 := below _ h3
  have n4 := below _ h4
  have n5 := below _ h5
  have n6 := below _ h6
  have n7 := below _ h7
  have ix := WAdm_WideIndices.indices q
  simp only [aspis_core.field.wide_exact.WideExact.from_limbs,
    ix.1,ix.2.1,ix.2.2.1,ix.2.2.2.1,ix.2.2.2.2.1,ix.2.2.2.2.2.1,
    ix.2.2.2.2.2.2.1,ix.2.2.2.2.2.2.2,bind_tc_ok,
    if_neg n0,if_neg n1,if_neg n2,if_neg n3,if_neg n4,if_neg n5,if_neg n6,if_neg n7]

#print axioms from_limbs
end AspisR1.WAdm_WideCarrier
end
