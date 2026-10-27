import RPu_AspisR1PoseidonPreparedChannelRunStepExact
import Aeneas.Std

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelArraySpecs
open Aeneas Aeneas.Std Result WP

/-- Checked read specification for a fixed-length Aeneas array. -/
theorem index_ok {α : Type} {n : Std.Usize}
    (a : Array α n) (i : Std.Usize) (hi : i.val < n.val) :
    ∃ x, Array.index_usize a i = .ok x ∧
      x = a.val[i.val]'(by simpa [a.property] using hi) := by
  have hb : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨x, hrun, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hb)
  exact ⟨x, hrun, by simpa using hvalue⟩

/-- Checked mutable-index opening, retaining the actual setter closure. -/
theorem index_mut_ok {α : Type} {n : Std.Usize}
    (a : Array α n) (i : Std.Usize) (hi : i.val < n.val) :
    ∃ row back, Array.index_mut_usize a i = .ok (row, back) ∧
      row = a.val[i.val]'(by simpa [a.property] using hi) ∧
      back = fun row => a.set i row := by
  have hb : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨out, hrun, hspec⟩ :=
    WP.spec_imp_exists (Array.index_mut_usize_spec a i hb)
  rcases out with ⟨row, back⟩
  rcases hspec with ⟨hrow, hback⟩
  exact ⟨row, back, hrun, by simpa using hrow, by simpa using hback⟩

#print axioms index_ok
#print axioms index_mut_ok
end AspisR1PoseidonPreparedChannelArraySpecs
