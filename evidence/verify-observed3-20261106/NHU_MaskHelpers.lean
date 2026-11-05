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

def addWord (a b : Nat) := if a+b≥2147483647 then a+b-2147483647 else a+b

def subWord (a b : Nat) := if a≥b then a-b else 2147483647-(b-a)

theorem addWord_eq (a b : Nat) (ha : a<2147483647) (hb : b<2147483647) :
 addWord a b=(a+b)%2147483647 := by unfold addWord;split <;> omega

theorem subWord_eq (a b : Nat) (ha : a<2147483647) (hb : b<2147483647) :
 subWord a b=(a+2147483647-b)%2147483647 := by unfold subWord;split <;> omega

def rNative (a b : Nat) :=
 (subWord (addWord a a) b, addWord a (addWord b b))

theorem rNative_eq (a b : Nat) (ha : a<2147483647) (hb : b<2147483647) :
 rNative a b=AspisR1.ExtractedMaskQM31Mul.rWords (a,b) := by
 have haa : addWord a a<2147483647 := by rw [addWord_eq a a ha ha];omega
 have hbb : addWord b b<2147483647 := by rw [addWord_eq b b hb hb];omega
 unfold rNative
 rw [subWord_eq _ b haa hb,addWord_eq a _ ha hbb,
     addWord_eq a a ha ha,addWord_eq b b hb hb]
 rfl

theorem cm_r (x : CM) (canonical : CanonicalCM x) :
 ∃ out,AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r x=ok out ∧
 CanonicalCM out ∧ wordsCM out=rNative x.a.val x.b.val := by
 obtain ⟨out,call,canon,words⟩:=
  AspisR1.ExtractedMaskBasisComponents.current_cm31_mul_r_words x canonical
 exact ⟨out,call,canon,words.trans (rNative_eq _ _ canonical.1 canonical.2).symm⟩

#print axioms addWord_eq
#print axioms subWord_eq
#print axioms rNative_eq
#print axioms cm_r

/-- Coordinate domains at BOTH actual coefficient-population loops. -/
theorem coordinate (column : Nat) : column%4<4 := Nat.mod_lt _ (by decide)

#print axioms negWord_eq
#print axioms cm_i
#print axioms cm_r_endpoint
#print axioms coordinate
end AspisR1.NHU_MaskHelpers
