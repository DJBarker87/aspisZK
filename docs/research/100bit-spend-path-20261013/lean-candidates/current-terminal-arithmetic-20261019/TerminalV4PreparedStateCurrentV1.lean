import TerminalV4CompositionLoopsChunk06V5
import TerminalV4TowerAddV2

set_option autoImplicit false
namespace AspisR1.TerminalV4PreparedStateCurrent
open Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev M31 := field.M31
abbrev CM := field.CM31
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Component := Aeneas.Std.Array M31 3#usize
abbrev P : Nat := AspisR1.TerminalV4TowerAdd.P
abbrev CanonicalCM := AspisR1.TerminalV4TowerAdd.CanonicalCM
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM

def ComponentFor (a : Component) (x : CM) : Prop :=
  ∃ s : M31, a = Array.make 3#usize [x.a, x.b, s] ∧
    s.val = (x.a.val + x.b.val) % P ∧ s.val < P

def PreparedFor (p : Prepared) (x : QM) : Prop :=
  ∃ t : CM, ∃ a b c : Component,
    field.CM31.add x.c0 x.c1 = .ok t ∧ CanonicalCM t ∧
    ComponentFor a x.c0 ∧ ComponentFor b x.c1 ∧ ComponentFor c t ∧
    p.components = Array.make 3#usize [a, b, c]

theorem current_component_new (x : CM) (hx : CanonicalCM x) :
    ∃ a : Component,
      field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
        () x = .ok a ∧ ComponentFor a x := by
  obtain ⟨s, hs, hv, hc⟩ := AspisR1.TerminalV4M31AddSub.current_add_mod x.a x.b hx.1 hx.2
  refine ⟨Array.make 3#usize [x.a, x.b, s], ?_, s, rfl, hv, hc⟩
  simp only [field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    hs, bind_tc_ok]

theorem current_prepared_new (x : QM) (hx : CanonicalQM x) :
    ∃ p : Prepared, field.PreparedQm31Multiplier.new x = .ok p ∧ PreparedFor p x := by
  obtain ⟨a, ha, hpa⟩ := current_component_new x.c0 hx.1
  obtain ⟨b, hb, hpb⟩ := current_component_new x.c1 hx.2
  obtain ⟨t, ht, hct, _, _⟩ := AspisR1.TerminalV4TowerAdd.current_cm_add_mod x.c0 x.c1 hx.1 hx.2
  obtain ⟨c, hc, hpc⟩ := current_component_new t hct
  refine ⟨⟨Array.make 3#usize [a, b, c]⟩, ?_, t, a, b, c, ht, hct, hpa, hpb, hpc, rfl⟩
  simp only [field.PreparedQm31Multiplier.new, ha, hb, ht, hc, bind_tc_ok]

#print axioms current_component_new
#print axioms current_prepared_new
end AspisR1.TerminalV4PreparedStateCurrent
