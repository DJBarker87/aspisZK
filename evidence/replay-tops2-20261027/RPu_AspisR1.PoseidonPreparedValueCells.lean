import ExtractedMaskPreparedState
import RPu_AspisR1PoseidonPreparedChannelArraySpecs

set_option autoImplicit false
namespace AspisR1PoseidonPreparedValueCells
open Aeneas.Std Result AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev CM := field.CM31
abbrev M31 := field.M31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Component := Array M31 3#usize
abbrev Components := Array Component 3#usize
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

private def at3 {α : Type} (a : Array α 3#usize) (i : Usize) (hi : i.val < 3) : α :=
  a.val[i.val]'(by simpa [a.property] using hi)

theorem prepared_components (p : Prepared) (x : QM)
    (hp : AspisR1.ExtractedMaskPreparedState.PreparedFor p x) :
    ∃ t s0 s1 s2,
      p.components = Array.make 3#usize [
        (Array.make 3#usize [x.c0.a, x.c0.b, s0] : Component),
        (Array.make 3#usize [x.c1.a, x.c1.b, s1] : Component),
        (Array.make 3#usize [t.a, t.b, s2] : Component)] ∧
      field.CM31.add x.c0 x.c1 = .ok t ∧
      s0.val = (x.c0.a.val + x.c0.b.val) % 2147483647 ∧
      s1.val = (x.c1.a.val + x.c1.b.val) % 2147483647 ∧
      s2.val = (t.a.val + t.b.val) % 2147483647 := by
  rcases hp with ⟨t,a,b,d,ht,htcan,ha,hb,hd,hcomponents⟩
  rcases ha with ⟨s0,haeq,hs0,_⟩
  rcases hb with ⟨s1,hbeq,hs1,_⟩
  rcases hd with ⟨s2,hdeq,hs2,_⟩
  refine ⟨t,s0,s1,s2,?_,ht,hs0,hs1,hs2⟩
  rw [hcomponents, haeq, hbeq, hdeq]

#print axioms prepared_components
end AspisR1PoseidonPreparedValueCells
