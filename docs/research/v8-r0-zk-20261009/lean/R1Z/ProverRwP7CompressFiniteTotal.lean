import R1Z.ProverRwP6CompressControl
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7CompressFiniteTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes] [ExternalFuns]

theorem read {T : Type} (xs : Slice T) (i : Usize)
    (bound : i.val < (Slice.len xs).val) :
    ∃ x, Slice.index_usize xs i = ok x := by
  have h : i.val < xs.val.length := bound
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem h]
  exact ⟨_,rfl⟩

-- All lengths and all raw accumulator/power values. Primitive totality is
-- exposed here and discharged for the selected release operations separately.
theorem finite_total (values : Slice M) (lambda : Q) (fuel : Nat)
    (out power : Q) (i : Usize) (bound : i.val+fuel=(Slice.len values).val)
    (scale : ∀ a b, ∃ c, aspis_core.field.QM31.mul_m31 a b = ok c)
    (add : ∀ a b, ∃ c, aspis_core.field.QM31.add a b = ok c)
    (mul : ∀ a b, ∃ c, aspis_core.field.QM31.mul a b = ok c) :
    ∃ result, finite values lambda fuel out power i = ok result := by
  induction fuel generalizing out power i with
  | zero =>
    have cap : ¬i < Slice.len values := by
      change ¬i.val < (Slice.len values).val
      omega
    exact ⟨out,by simp only [finite,dispatch,cap,if_false]⟩
  | succ fuel ih =>
    have hi : i.val < (Slice.len values).val := by omega
    obtain ⟨m,hm⟩ := read values i hi
    obtain ⟨q,hq⟩ := scale power m
    obtain ⟨a,ha⟩ := add out q
    obtain ⟨p,hp⟩ := mul power lambda
    have step : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize=i.val+1
      apply Nat.mod_eq_of_lt
      have big := (Slice.len values).hSize
      omega
    obtain ⟨r,hr⟩ := ih a p (Usize.wrapping_add i 1#usize) (by omega)
    refine ⟨r,?_⟩
    simp only [finite,dispatch,show i < Slice.len values from hi,if_true,hm,hq,ha,hp,bind_tc_ok]
    exact hr
#print axioms read
#print axioms finite_total
end R1Z.ProverRwP7CompressFiniteTotal
