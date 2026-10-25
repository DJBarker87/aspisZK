import WAdm_Domain
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_WideCarrier
open OraclePortCkptAbi2Extracted OraclePortCkptAbi4Decode
abbrev E := aspis_core.field.wide_exact.WideExact

def limbs (q : E) : Array U32 8#usize :=
  Array.make 8#usize [q.c0.c0.a,q.c0.c0.b,q.c0.c1.a,q.c0.c1.b,
    q.c1.c0.a,q.c1.c0.b,q.c1.c1.a,q.c1.c1.b]

attribute [local irreducible] aspis_core.field.wide_exact.WideExact.from_limbs limbs

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
  trace_state
  simp (disch := scalar_tac) [aspis_core.field.wide_exact.WideExact.from_limbs,
    limbs,Array.make,Array.index_usize,lift,n0,n1,n2,n3,n4,n5,n6,n7]

#print axioms from_limbs
end AspisR1.WAdm_WideCarrier
end
