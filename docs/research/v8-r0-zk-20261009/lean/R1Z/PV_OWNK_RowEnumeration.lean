import R1Z.PV_OWNK_ConcreteDecoder
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNK_RowEnumeration
open scoped BigOperators
open PV_OWNI_DensePrune

def tail (n : Nat) (a : Fin (2^n)) (i : Fin n) : Bool := a.val.testBit (n-1-i.val)

theorem tail_injective (n : Nat) : Function.Injective (tail n) := by
 intro a b h
 apply Fin.ext
 apply Nat.eq_of_testBit_eq
 intro i
 by_cases hi : i<n
 · have hv := congrFun h (⟨n-1-i,by omega⟩ : Fin n)
   have he : n-1-(n-1-i)=i := by omega
   simpa only [tail,he] using hv
 · have hp : 2^n≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
   rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hp),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hp)]

def join (w t : Nat) (z : Fin (2^w) × Fin (2^t)) : Fin (2^(w+t)) :=
 ⟨PV_RDB2D_SparseAddress.row z.1.val t z.2.val,by
  unfold PV_RDB2D_SparseAddress.row
  rw [Nat.pow_add]
  calc
   z.1.val*2^t+z.2.val < (z.1.val+1)*2^t := by
    have := z.2.isLt
    rw [Nat.add_mul,Nat.one_mul]; omega
   _ ≤ 2^w*2^t := Nat.mul_le_mul_right _ z.1.isLt⟩

theorem join_injective (w t : Nat) : Function.Injective (join w t) := by
 intro a b h
 have ha := PV_OWNJ_Rows.row_decode a.1.val t a.2.val a.2.isLt
 have hb := PV_OWNJ_Rows.row_decode b.1.val t b.2.val b.2.isLt
 have hq := congrArg (fun r : Fin (2^(w+t)) => r.val / 2^t) h
 have hr := congrArg (fun r : Fin (2^(w+t)) => r.val % 2^t) h
 dsimp only [join] at hq hr
 rw [ha.1,hb.1] at hq
 rw [ha.2,hb.2] at hr
 exact Prod.ext (Fin.ext hq) (Fin.ext hr)

theorem join_bijective (w t : Nat) : Function.Bijective (join w t) := by
 refine ⟨join_injective w t,?_⟩
 by_contra hn
 have hc := Fintype.card_lt_of_injective_not_surjective (join w t) (join_injective w t) hn
 simp only [Fintype.card_prod,Fintype.card_fin,Nat.pow_add] at hc
 exact (Nat.lt_irrefl _ hc)

def rowEquiv (w t : Nat) : (Fin (2^w) × Fin (2^t)) ≃ Fin (2^(w+t)) :=
 Equiv.ofBijective (join w t) (join_bijective w t)

theorem sum_join {K : Type} [AddCommMonoid K] (w t : Nat)
 (f : Fin (2^(w+t)) → K) :
 (∑ r, f r) = ∑ a : Fin (2^w), ∑ b : Fin (2^t), f (join w t (a,b)) := by
 rw [← Equiv.sum_comp (rowEquiv w t) f]
 simp only [Fintype.sum_prod_type]
 rfl

/-- Dense evaluation in split coordinates, using every row of the integer
cube. The scanner's List-to-product and suffix-code identities are separate. -/
def denseSplit {K : Type} [Field K] (w t : Nat) (p : Fin w → K)
 (suffix : Fin (2^t)) (column : Fin (2^(w+t)) → K) : K :=
 ∑ r, let z := (rowEquiv w t).symm r
  weight p (tail w z.1) *
   weight (fun j => if tail t suffix j then (1:K) else 0) (tail t z.2) * column r

theorem dense_sparse {K : Type} [Field K] (w t : Nat) (p : Fin w → K)
 (suffix : Fin (2^t)) (column : Fin (2^(w+t)) → K) :
 denseSplit w t p suffix column =
 ∑ a : Fin (2^w), weight p (tail w a) * column (join w t (a,suffix)) := by
 classical
 have hi (z : Fin (2^w) × Fin (2^t)) : (rowEquiv w t).symm (join w t z) = z :=
  (rowEquiv w t).symm_apply_apply z
 have hb (b : Fin (2^t)) :
  weight (fun j => if tail t suffix j then (1:K) else 0) (tail t b) =
  if b=suffix then 1 else 0 := by
  rw [boolean_weight]
  by_cases h : b=suffix
  · subst b; rw [if_pos rfl,if_pos rfl]
  · rw [if_neg (fun he => h (tail_injective t he)),if_neg h]
 unfold denseSplit
 rw [sum_join]
 simp only [hi]
 apply Finset.sum_congr rfl
 intro a ha
 simp [hb]
#print axioms tail_injective
#print axioms join_injective
#print axioms join_bijective
#print axioms sum_join
#print axioms dense_sparse
end R1Z.PV_OWNK_RowEnumeration
