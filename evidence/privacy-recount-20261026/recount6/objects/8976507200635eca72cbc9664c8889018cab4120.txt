import PV_B1_PoleEqual
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleKeep
open Aeneas Aeneas.Std Result PV_B1_258
abbrev Q := aspis_core.field.QM31
local instance : DecidableEq Q := Classical.decEq _

theorem equal_source (a b : Q) : equal a b = ok (decide (a=b)) := by
  rw [PV_B1_PoleEqual.source]
  have h := propext (PV_B1_PoleEqual.zero a b)
  simp only [h]

theorem source (clear active : Bool) (chi value : Q) :
    keep_clear clear active chi value = ok (clear && !(active && decide (chi=value))) := by
  simp only [keep_clear,equal_source,bind_tc_ok]
  cases clear <;> cases active <;> cases (decide (chi=value)) <;> rfl

theorem inactive (clear : Bool) (chi value : Q) :
    keep_clear clear false chi value = ok clear := by
  rw [source]
  cases clear <;> rfl

theorem absorbing (active : Bool) (chi value : Q) :
    keep_clear false active chi value = ok false := by
  rw [source]
  rfl
#print axioms equal_source
#print axioms source
#print axioms inactive
#print axioms absorbing
end PV_B1_PoleKeep
