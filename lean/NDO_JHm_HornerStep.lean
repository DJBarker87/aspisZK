import NDO_JHm_Arithmetic
set_option autoImplicit false
namespace AspisR1.JHm_HornerStep
/-- Abstract semiring step: the field representation is never unfolded. -/
theorem source {F : Type} [CommSemiring F] (x g : F) (xs : List F) :
    x+g*(∑ j : Fin xs.length,g^j.val*xs[j.val])=
      ∑ j : Fin (xs.length+1),g^j.val*(x::xs)[j.val] := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_mul,List.getElem_cons_zero,Fin.val_succ,
    List.getElem_cons_succ,pow_succ]
  rw [Finset.mul_sum]
  apply congrArg (fun z : F => x+z)
  apply Finset.sum_congr rfl
  intro j hj
  exact (mul_assoc g (g^j.val) xs[j.val]).symm.trans
    (congrArg (fun z : F => z*xs[j.val]) (mul_comm g (g^j.val)))
#print axioms source
end AspisR1.JHm_HornerStep
