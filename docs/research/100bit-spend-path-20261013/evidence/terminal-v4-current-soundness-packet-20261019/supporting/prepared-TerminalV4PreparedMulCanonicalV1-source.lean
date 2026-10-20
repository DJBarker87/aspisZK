import TerminalV4PreparedComponentCurrentV4
import TerminalV4PreparedStateCurrentV1
import TerminalV4TowerAddV2

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.TerminalV4PreparedMulCanonical
open Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.TerminalV4PreparedStateCurrent
abbrev QM := field.QM31
abbrev CM := field.CM31
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev CanonicalCM := AspisR1.TerminalV4TowerAdd.CanonicalCM

@[simp] private theorem component_index0 {α : Type} (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 0#usize = .ok a := rfl
@[simp] private theorem component_index1 {α : Type} (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 1#usize = .ok b := rfl
@[simp] private theorem component_index2 {α : Type} (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 2#usize = .ok c := rfl

theorem mul_by_r_canonical (x : CM) (hx : CanonicalCM x) :
    ∃ z, field.mul_by_r x = .ok z ∧ CanonicalCM z := by
  obtain ⟨m, hm, _, hcm⟩ := AspisR1.TerminalV4M31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a, ha, _, hca⟩ := AspisR1.TerminalV4M31AddSub.current_sub_mod m x.b hcm hx.2
  obtain ⟨m2, hm2, _, hcm2⟩ := AspisR1.TerminalV4M31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b, hb, _, hcb⟩ := AspisR1.TerminalV4M31AddSub.current_add_mod x.a m2 hx.1 hcm2
  refine ⟨⟨a,b⟩, ?_, ⟨hca,hcb⟩⟩
  simp only [field.mul_by_r, field.M31.double, hm, ha, hm2, hb, bind_tc_ok]

theorem prepared_mul_canonical (p : field.PreparedQm31Multiplier) (x y : QM)
    (hx : CanonicalQM x) (hy : CanonicalQM y) (hp : PreparedFor p x) :
    ∃ z, field.PreparedQm31Multiplier.mul p y = .ok z ∧ CanonicalQM z := by
  obtain ⟨t, a, b, c, hsum, htc, ha, hb, hc, hcomponents⟩ := hp
  obtain ⟨m0, hm0, hcm0⟩ := AspisR1.TerminalV4PreparedComponentCurrent.current_component_mul_canonical
    a x.c0 y.c0 hx.1 hy.1 ha
  obtain ⟨m1, hm1, hcm1⟩ := AspisR1.TerminalV4PreparedComponentCurrent.current_component_mul_canonical
    b x.c1 y.c1 hx.2 hy.2 hb
  obtain ⟨t', hsum', ht', _hv⟩ := AspisR1.TerminalV4TowerAdd.current_cm_add_mod y.c0 y.c1 hy.1 hy.2
  obtain ⟨m2, hm2, hcm2⟩ := AspisR1.TerminalV4PreparedComponentCurrent.current_component_mul_canonical
    c t t' htc ht' hc
  obtain ⟨r, hr, hrc⟩ := mul_by_r_canonical m1 hcm1
  obtain ⟨sum, hsumOut, hsumCan, _, _⟩ :=
    AspisR1.TerminalV4TowerAdd.current_cm_add_mod m0 r hcm0 hrc
  obtain ⟨d, hd, hdCan, _, _⟩ :=
    AspisR1.TerminalV4TowerAdd.current_cm_sub_mod m2 m0 hcm2 hcm0
  obtain ⟨high, hhigh, hhighCan, _, _⟩ :=
    AspisR1.TerminalV4TowerAdd.current_cm_sub_mod d m1 hdCan hcm1
  refine ⟨⟨sum, high⟩, ?_, ⟨hsumCan, hhighCan⟩⟩
  rw [field.PreparedQm31Multiplier.mul]
  simp only [hcomponents, component_index0, component_index1, component_index2,
    hm0, hm1, hsum', hm2, hr, hsumOut, hd, hhigh, bind_tc_ok]

#print axioms mul_by_r_canonical
#print axioms prepared_mul_canonical
end AspisR1.TerminalV4PreparedMulCanonical
