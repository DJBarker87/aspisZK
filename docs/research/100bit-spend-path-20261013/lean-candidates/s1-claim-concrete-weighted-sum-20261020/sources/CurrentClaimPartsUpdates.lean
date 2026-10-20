import CurrentClaimCallerComposition
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimParts
open Concrete

theorem set_cell (parts : Array E 7#usize) (i : Usize) (value : E) (hi : i.val<7)
    (j : Usize) (hj : j.val<7) :
    cell (parts.set i value) j hj = if j.val=i.val then value else cell parts j hj := by
  cases parts with
  | mk xs hxs =>
    have hn : xs.length=7 := by simpa using hxs
    have hjList : j.val<xs.length := by omega
    change (xs.set i.val value)[j.val]'(by simpa [List.length_set,hxs] using hjList) = _
    rw [List.getElem_set (h := by simpa [List.length_set] using hjList)]
    by_cases he : j.val=i.val
    · simp only [he,ite_true]
    · have hne : i.val≠j.val := fun h => he h.symm
      rw [if_neg hne]
      change xs[j.val]'hjList = if j.val=i.val then value else xs[j.val]'hjList
      rw [if_neg he]

theorem update_cells (parts out : Array E 7#usize) (i : Usize) (value : E)
    (hi : i.val<7) (hwrite : Array.update parts i value=Result.ok out) :
    ∀ j (hj : j.val<7), cell out j hj = if j.val=i.val then value else cell parts j hj := by
  obtain ⟨out',hr,he⟩ := WP.spec_imp_exists
    (Array.update_spec parts i value (by simpa [parts.property] using hi))
  have hout : out=parts.set i value := (Result.ok.inj (hwrite.symm.trans hr)).trans he
  subst out
  exact set_cell parts i value hi

theorem add_one_success_val (point i : Usize) (hp : point.val<6)
    (h : (point+1#usize : Result Usize)=Result.ok i) : i.val=point.val+1 := by
  have hmax : 7≤Usize.max := by scalar_tac
  have hb : point.val+1≤Usize.max := by omega
  have hs : (point+1#usize : Result Usize) ⦃ j => j.val=point.val+1 ⦄ := by
    apply UScalar.add_spec
    simpa only [show (1#usize).val=1 from by rfl,UScalar.max_USize_eq] using hb
  rw [h,WP.spec_ok] at hs
  exact hs

#print axioms set_cell
#print axioms update_cells
#print axioms add_one_success_val
end AspisR1CurrentPreparedClaim.ClaimParts
