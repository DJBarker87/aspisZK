import TerminalV4PreparedStateCurrentV1
import TerminalV4ReducerV1
import TerminalV4M31AddSubV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.TerminalV4PreparedComponentCurrent
open Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.TerminalV4PreparedStateCurrent
abbrev P : Nat := AspisR1.TerminalV4M31AddSub.P

theorem current_component_mul_canonical
    (a : Component) (x y : CM)
    (hx : CanonicalCM x) (hy : CanonicalCM y) (hp : ComponentFor a x) :
    ∃ z : CM,
      field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (a, y) = .ok z ∧ CanonicalCM z := by
  obtain ⟨s, rfl, hs, _hscan⟩ := hp
  obtain ⟨t, ht, hvt, _⟩ := AspisR1.TerminalV4M31AddSub.current_add_mod y.a y.b hy.1 hy.2
  obtain ⟨m0, h0, _, hc0⟩ := AspisR1.TerminalV4Reducer.current_mul_mod x.a y.a
  obtain ⟨m1, h1, _, hc1⟩ := AspisR1.TerminalV4Reducer.current_mul_mod x.b y.b
  obtain ⟨m2, h2, _, hc2⟩ := AspisR1.TerminalV4Reducer.current_mul_mod s t
  obtain ⟨low, hl, _, hcl⟩ := AspisR1.TerminalV4M31AddSub.current_sub_mod m0 m1 hc0 hc1
  obtain ⟨high0, hh0, _, hch0⟩ := AspisR1.TerminalV4M31AddSub.current_sub_mod m2 m0 hc2 hc0
  obtain ⟨high, hh, _, hch⟩ := AspisR1.TerminalV4M31AddSub.current_sub_mod high0 m1 hch0 hc1
  refine ⟨⟨low, high⟩, ?_, ⟨hcl, hch⟩⟩
  simp only [field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
    index0, index1, index2, h0, h1, ht, h2, hl, hh0, hh, bind_tc_ok]

#print axioms current_component_mul_canonical
end AspisR1.TerminalV4PreparedComponentCurrent
