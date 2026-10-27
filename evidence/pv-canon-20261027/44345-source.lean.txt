import R1Z.PV_Canon_Carrier
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std ProverRwFull
 def limbs (q : aspis_core.field.QM31) : List U32 := [q.c0.a,q.c0.b,q.c1.a,q.c1.b]
 theorem quartic_iff_limbs (q : aspis_core.field.QM31) : Q q ↔ ∀ x ∈ limbs q, M x := by
  simp only [limbs,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,Q,C]
 theorem polynomial_iff_limbs (p : Array aspis_core.field.QM31 28#usize) :
    Coeffs p ↔ ∀ x ∈ p.val.flatMap limbs, M x := by
  constructor
  · intro h x hx
    obtain ⟨q,hq,hx⟩ := List.mem_flatMap.mp hx
    exact (quartic_iff_limbs q).mp (h q hq) x hx
  · intro h q hq
    apply (quartic_iff_limbs q).mpr
    intro x hx
    exact h x (List.mem_flatMap.mpr ⟨q,hq,hx⟩)
 theorem argument_limb_count (p : Array aspis_core.field.QM31 28#usize) (q : aspis_core.field.QM31) :
    (p.val.flatMap limbs ++ limbs q).length = 116 := by
  have helper : ∀ xs : List aspis_core.field.QM31, (xs.flatMap limbs).length=4*xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.flatMap_cons,List.length_append,limbs,List.length_cons,List.length_nil,ih]; omega
  rw [List.length_append,helper]
  have hp : p.val.length=28 := p.property
  simp only [limbs,List.length_cons,List.length_nil,hp]
#print axioms quartic_iff_limbs
#print axioms polynomial_iff_limbs
#print axioms argument_limb_count
end R1Z.PV_Canon
