import RPz7_WAdm_Domain
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_WideIndices
open OraclePortCkptAbi2Extracted
abbrev E := aspis_core.field.wide_exact.WideExact

def limbs (q : E) : Array U32 8#usize :=
  Array.make 8#usize [q.c0.c0.a,q.c0.c0.b,q.c0.c1.a,q.c0.c1.b,
    q.c1.c0.a,q.c1.c0.b,q.c1.c1.a,q.c1.c1.b]

theorem indices (q : E) :
    Array.index_usize (limbs q) 0#usize = ok q.c0.c0.a ∧
    Array.index_usize (limbs q) 1#usize = ok q.c0.c0.b ∧
    Array.index_usize (limbs q) 2#usize = ok q.c0.c1.a ∧
    Array.index_usize (limbs q) 3#usize = ok q.c0.c1.b ∧
    Array.index_usize (limbs q) 4#usize = ok q.c1.c0.a ∧
    Array.index_usize (limbs q) 5#usize = ok q.c1.c0.b ∧
    Array.index_usize (limbs q) 6#usize = ok q.c1.c1.a ∧
    Array.index_usize (limbs q) 7#usize = ok q.c1.c1.b := by
  simp (disch := scalar_tac) [limbs,Array.make,Array.index_usize]

#print axioms indices
end AspisR1.WAdm_WideIndices
end
