import R1Z.PV_PoleLeafValue
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_PoleLeafCorrect
open Aeneas Aeneas.Std Result
open PV_PoleLeafValue
attribute [local instance] Classical.propDecidable

theorem equal (a b : Q) : PV_PoleLeafSource.ct_pole.equal a b = ok (decide (a=b)) := by
  rw [source]
  have h := propext (zero a b)
  simp only [h]

theorem keep_clear (clear active : Bool) (chi value : Q) :
    PV_PoleLeafSource.ct_pole.keep_clear clear active chi value =
      ok (clear && !(active && (chi=value))) := by
  simp only [PV_PoleLeafSource.ct_pole.keep_clear,equal,bind_tc_ok]
  cases clear <;> cases active <;> cases (decide (chi=value)) <;> rfl

theorem inactive (clear : Bool) (chi value : Q) :
    PV_PoleLeafSource.ct_pole.keep_clear clear false chi value = ok clear := by
  rw [keep_clear]
  cases clear <;> rfl

theorem absorbing (active : Bool) (chi value : Q) :
    PV_PoleLeafSource.ct_pole.keep_clear false active chi value = ok false := by
  rw [keep_clear]
  rfl
#print axioms equal
#print axioms keep_clear
#print axioms inactive
#print axioms absorbing
end R1Z.PV_PoleLeafCorrect
