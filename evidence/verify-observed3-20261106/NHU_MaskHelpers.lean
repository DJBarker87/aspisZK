import NHG_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_MaskHelpers
open AspisR1.ExtractedMaskTowerAdd
abbrev CM := AspisR1SelectedMaskProbe.field.CM31
abbrev QM := AspisR1SelectedMaskProbe.field.QM31

def negWord (x : Nat) := if x=0 then 0 else 2147483647-x

theorem negWord_eq (x : Nat) (canonical : x<2147483647) :
 negWord x=(2147483647-x)%2147483647 := by
 unfold negWord
 split <;> omega

/-- Exact natural returned words consumed by the native CM31 i helper.
No decoder, parent acceptance or chosen success is assumed. -/
theorem cm_i (x : CM) (canonical : CanonicalCM x) :
 ∃ out,AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_i x=ok out ∧
 CanonicalCM out ∧ wordsCM out=(negWord x.b.val,x.a.val) := by
 obtain ⟨out,call,canon,words⟩:=
  AspisR1.ExtractedMaskBasisComponents.current_cm31_mul_i_words x canonical
 refine ⟨out,call,canon,?_⟩
 rw [words,negWord_eq x.b.val canonical.2]

/-- Native add-only helper's adopted emitted endpoint is the actual
mul_by_r operation; no multiplication verification is needed in Kani. -/
theorem cm_r_endpoint (x : CM) :
 AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r x=
 AspisR1SelectedMaskProbe.field.mul_by_r x :=
 AspisR1.ExtractedMaskBasisComponents.cm31_mul_r_eq_mul_by_r x

/-- Coordinate domains at BOTH actual coefficient-population loops. -/
theorem coordinate (column : Nat) : column%4<4 := Nat.mod_lt _ (by decide)

#print axioms negWord_eq
#print axioms cm_i
#print axioms cm_r_endpoint
#print axioms coordinate
end AspisR1.NHU_MaskHelpers
