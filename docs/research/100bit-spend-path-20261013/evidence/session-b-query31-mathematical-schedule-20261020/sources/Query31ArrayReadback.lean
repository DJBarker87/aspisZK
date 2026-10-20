import Aeneas.Std

open Aeneas Aeneas.Std Result WP
set_option autoImplicit false

namespace AspisR1PublicPreparation.Query31SourceSchedule

/-- Successful fixed-index update writes the supplied element at that index. -/
theorem update_readback {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (v : α) (hi : i.val < n.val)
    (out : Array α n) (h : Array.update a i v = ok out) :
    Array.index_usize out i = ok v := by
  have hlen : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨updated, hu, hset⟩ := WP.spec_imp_exists (Array.update_spec a i v hlen)
  have hout : out = updated := Result.ok.inj (h.symm.trans hu)
  subst out
  have hlen' : i.val < updated.length := by simpa [updated.property] using hi
  obtain ⟨x, hx, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec updated i hlen')
  have hxv : x = v := by simpa [hset, Array.set_val_eq] using hvalue
  rw [hxv] at hx
  exact hx

/-- The actual setter closure returned by `index_mut_usize` writes back at
its selected slot, retaining the generated update semantics. -/
theorem index_mut_readback {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (v old : α) (back : α → Array α n)
    (hi : i.val < n.val)
    (h : Array.index_mut_usize a i = ok (old, back)) :
    Array.index_usize (back v) i = ok v := by
  have hlen : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨out, hmut, hspec⟩ := WP.spec_imp_exists (Array.index_mut_usize_spec a i hlen)
  rcases out with ⟨old', back'⟩
  rcases hspec with ⟨_, hback⟩
  have heq : (old', back') = (old, back) := Result.ok.inj (hmut.symm.trans h)
  have hbackEq : back = fun x => a.set i x := by
    have hsnd := congrArg Prod.snd heq
    exact hsnd.symm.trans hback
  subst back
  have hlen' : i.val < (a.set i v).length := by simpa using hlen
  obtain ⟨x, hx, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec (a.set i v) i hlen')
  have hxv : x = v := by simpa using hvalue
  rw [hxv] at hx
  change Array.index_usize (a.set i v) i = ok v at hx
  exact hx

#print axioms update_readback
#print axioms index_mut_readback

/-- A successful update preserves reads at every distinct index. -/
theorem update_readback_other {α : Type} {n : Usize}
    (a : Array α n) (i j : Usize) (v : α) (hij : i ≠ j)
    (hi : i.val < n.val) (hj : j.val < n.val) (out : Array α n)
    (h : Array.update a i v = ok out) :
    Array.index_usize out j = Array.index_usize a j := by
  have hi' : i.val < a.length := by simpa [a.property] using hi
  have hlenj : j.val < a.length := by simpa [a.property] using hj
  obtain ⟨updated, hu, hset⟩ := WP.spec_imp_exists (Array.update_spec a i v hi' )
  have hout : out = updated := Result.ok.inj (h.symm.trans hu)
  subst out
  have hlenj' : j.val < updated.length := by simpa [updated.property] using hj
  obtain ⟨x, hx, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec updated j hlenj')
  obtain ⟨y, hy, hbase⟩ := WP.spec_imp_exists (Array.index_usize_spec a j hlenj)
  have hsetjArray := Array.getElem_set_neq a i j v
    (by simpa [a.property] using hj) hij
  have hsetj : (a.val.set i.val v)[j.val]'(by simpa [a.property] using hj) =
      a.val[j.val]'hlenj := by simpa [Array.set_val_eq] using hsetjArray
  have hx' : x = (a.val.set i.val v)[j.val]'(by simpa [a.property] using hj) := by
    simpa [hset] using hvalue
  have hy' : y = a.val[j.val]'hlenj := by simpa using hbase
  have hxy : x = y := by
    calc
      x = (a.val.set i.val v)[j.val]'(by simpa [a.property] using hj) := hx'
      _ = a.val[j.val]'hlenj := hsetj
      _ = y := hy'.symm
  rw [hxy] at hx
  exact hx.trans hy.symm

#print axioms update_readback_other

end AspisR1PublicPreparation.Query31SourceSchedule
