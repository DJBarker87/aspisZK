import ExtractedMaskPreparedState
import ExtractedMaskQM31Exact

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedStateUnique
open Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisV8R15.ExactTowerBase

abbrev QM := field.QM31
abbrev CM := field.CM31
abbrev M31 := field.M31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Component := AspisR1.ExtractedMaskPreparedState.Component
abbrev ComponentFor := AspisR1.ExtractedMaskPreparedState.ComponentFor
abbrev PreparedFor := AspisR1.ExtractedMaskPreparedState.PreparedFor

private theorem componentFor_coords (a : Component) (x : CM)
    (h : ComponentFor a x) : a.val[0]'(by scalar_tac) = x.a ∧ a.val[1]'(by scalar_tac) = x.b := by
  rcases h with ⟨s, ha, _, _⟩
  constructor
  · have h0 := congrArg (fun z : Component => z.val[0]'(by scalar_tac)) ha
    simpa [Array.make] using h0
  · have h1 := congrArg (fun z : Component => z.val[1]'(by scalar_tac)) ha
    simpa [Array.make] using h1

theorem preparedFor_unique (p : Prepared) (x y : QM)
    (hx : PreparedFor p x) (hy : PreparedFor p y) : x = y := by
  rcases hx with ⟨t,a,b,c, ht, htc, hpa,hpb,hpc,harr⟩
  rcases hy with ⟨t',a',b',c', ht', htc', hpa',hpb',hpc',harr'⟩
  have houter : Array.make 3#usize [a,b,c] = Array.make 3#usize [a',b',c'] :=
    harr.symm.trans harr'
  have ha : a = a' := by
    have h := congrArg (fun z : Array Component 3#usize => z.val[0]'(by scalar_tac)) houter
    simpa [Array.make] using h
  have hb : b = b' := by
    have h := congrArg (fun z : Array Component 3#usize => z.val[1]'(by scalar_tac)) houter
    simpa [Array.make] using h
  have h0 := componentFor_coords a x.c0 hpa
  have h0' := componentFor_coords a' y.c0 hpa'
  have h1 := componentFor_coords b x.c1 hpb
  have h1' := componentFor_coords b' y.c1 hpb'
  have hxa : x.c0.a = y.c0.a := by
    have := congrArg (fun z : Component => z.val[0]'(by scalar_tac)) ha
    exact h0.1.symm.trans (this.trans h0'.1)
  have hxb : x.c0.b = y.c0.b := by
    have := congrArg (fun z : Component => z.val[1]'(by scalar_tac)) ha
    exact h0.2.symm.trans (this.trans h0'.2)
  have hya : x.c1.a = y.c1.a := by
    have := congrArg (fun z : Component => z.val[0]'(by scalar_tac)) hb
    exact h1.1.symm.trans (this.trans h1'.1)
  have hyb : x.c1.b = y.c1.b := by
    have := congrArg (fun z : Component => z.val[1]'(by scalar_tac)) hb
    exact h1.2.symm.trans (this.trans h1'.2)
  cases x with
  | mk xc0 xc1 =>
    cases y with
    | mk yc0 yc1 =>
      simp only [field.QM31] at hxa hxb hya hyb
      cases xc0 with
      | mk xa xb =>
        cases yc0 with
        | mk ya yb =>
          cases xc1 with
          | mk xc xd =>
            cases yc1 with
            | mk yc yd =>
              simp_all

#print axioms preparedFor_unique
end AspisR1.PoseidonPreparedStateUnique
