import AspisR1S9HelperP6.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S9ArrayWriteScheduleRootV1
variable {α : Type}
abbrev Four := 4#usize

def cells (a : Array α Four) (j : Fin 4) : α :=
  a.val[j.val]'(by simpa [a.property] using j.isLt)

/-- The checked array update determines every output cell, including its frame. -/
theorem update_cells (a out : Array α Four) (i : Usize) (x : α)
    (hi : i.val < 4) (h : Array.update a i x = .ok out) (j : Fin 4) :
    cells out j = if j.val = i.val then x else cells a j := by
  obtain ⟨expected, hexpected, hval⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa [a.property] using hi))
  have hout : out = expected := Result.ok.inj (h.symm.trans hexpected)
  subst out
  cases hval
  change (a.val.set i.val x)[j.val]'_ = _
  by_cases hij : i.val = j.val
  · rw [if_pos hij.symm]
    simpa [hij] using List.getElem_set_self (l := a.val) (i := i.val) (a := x)
      (by simpa [a.property] using hi)
  · rw [if_neg (Ne.symm hij)]
    exact List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val) hij _

/-- Exact five writes across the helper's two branches. No arithmetic result
or starting cell can alter the positions not assigned by that source schedule. -/
theorem two_side_write_cells
    (initial a b c d out : Array α Four) (v0 v1 v1' v2 v3 : α)
    (h0 : Array.update initial 0#usize v0 = .ok a)
    (h1 : Array.update a 1#usize v1 = .ok b)
    (h1' : Array.update b 1#usize v1' = .ok c)
    (h2 : Array.update c 2#usize v2 = .ok d)
    (h3 : Array.update d 3#usize v3 = .ok out) (j : Fin 4) :
    cells out j = if j.val = 0 then v0 else if j.val = 1 then v1'
      else if j.val = 2 then v2 else v3 := by
  rw [update_cells d out 3#usize v3 (by decide) h3 j,
      update_cells c d 2#usize v2 (by decide) h2 j,
      update_cells b c 1#usize v1' (by decide) h1' j,
      update_cells a b 1#usize v1 (by decide) h1 j,
      update_cells initial a 0#usize v0 (by decide) h0 j]
  change (if j.val = 3 then v3 else if j.val = 2 then v2 else
    if j.val = 1 then v1' else if j.val = 1 then v1 else
    if j.val = 0 then v0 else cells initial j) = _
  have hcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
    have hj := j.isLt
    omega
  rcases hcases with h | h | h | h <;> simp [h]

#print axioms update_cells
#print axioms two_side_write_cells
end AspisR1.S9ArrayWriteScheduleRootV1
