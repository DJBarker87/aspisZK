import TerminalV4PreparedComponentCurrentV4
import TerminalV4QM31MulCurrent
import TerminalV4QM31TowerCurrent
import TerminalV4CM31MulCurrent

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.TerminalV4PreparedMulExactCurrent
open Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.TerminalV4PreparedStateCurrent
abbrev QM := field.QM31
abbrev CM := field.CM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev CanonicalCM := AspisR1.TerminalV4TowerAdd.CanonicalCM
abbrev PreparedFor := AspisR1.TerminalV4PreparedStateCurrent.PreparedFor
abbrev Component := AspisR1.TerminalV4PreparedStateCurrent.Component

@[simp] private theorem index0 {α : Type} (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 0#usize = .ok a := rfl
@[simp] private theorem index1 {α : Type} (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 1#usize = .ok b := rfl
@[simp] private theorem index2 {α : Type} (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 2#usize = .ok c := rfl

@[simp] private theorem componentIndex0 {α : Type} (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 0#usize = .ok a := rfl
@[simp] private theorem componentIndex1 {α : Type} (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 1#usize = .ok b := rfl
@[simp] private theorem componentIndex2 {α : Type} (a b c : α) :
    Array.index_usize (Array.make 3#usize [a,b,c]) 2#usize = .ok c := rfl

private theorem cm_eq_of_words (x y : CM)
    (h : (x.a.val, x.b.val) = (y.a.val, y.b.val)) : x = y := by
  have ha := UScalar.val_eq_imp x.a y.a (congrArg Prod.fst h)
  have hb := UScalar.val_eq_imp x.b y.b (congrArg Prod.snd h)
  cases x with
  | mk xa xb =>
    cases y with
    | mk ya yb =>
      dsimp at ha hb
      cases ha
      cases hb
      rfl

theorem current_component_mul_words
    (a : Component) (x y : CM)
    (hx : CanonicalCM x) (hy : CanonicalCM y) (hp : ComponentFor a x) :
    ∃ z : CM,
      field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (a, y) = .ok z ∧ CanonicalCM z ∧
      (z.a.val, z.b.val) = AspisR1.TerminalV4QM31MulCurrent.mulWords
        (AspisR1.TerminalV4TowerAdd.wordsCM x)
        (AspisR1.TerminalV4TowerAdd.wordsCM y) := by
  obtain ⟨s, rfl, hs, _hscan⟩ := hp
  obtain ⟨t, ht, hvt, _⟩ := AspisR1.TerminalV4M31AddSub.current_add_mod y.a y.b hy.1 hy.2
  obtain ⟨m0, h0, hv0, hc0⟩ := AspisR1.TerminalV4Reducer.current_mul_mod x.a y.a
  obtain ⟨m1, h1, hv1, hc1⟩ := AspisR1.TerminalV4Reducer.current_mul_mod x.b y.b
  obtain ⟨m2, h2, hv2, hc2⟩ := AspisR1.TerminalV4Reducer.current_mul_mod s t
  have hv2' : m2.val = ((x.a.val + x.b.val) * (y.a.val + y.b.val)) %
      AspisR1.TerminalV4QM31MulCurrent.P := by
    rw [hv2, hs, hvt]
    exact (Nat.mul_mod _ _ _).symm
  obtain ⟨low, hl, hvl, hcl⟩ :=
    AspisR1.TerminalV4M31AddSub.current_sub_mod m0 m1 hc0 hc1
  obtain ⟨high0, hh0, hvh0, hch0⟩ :=
    AspisR1.TerminalV4M31AddSub.current_sub_mod m2 m0 hc2 hc0
  obtain ⟨high, hh, hvh, hch⟩ :=
    AspisR1.TerminalV4M31AddSub.current_sub_mod high0 m1 hch0 hc1
  refine ⟨⟨low, high⟩, ?_, ⟨hcl, hch⟩, ?_⟩
  · rw [AspisR1.TerminalV4PreparedComponentCurrent.current_call_eq]
    simp only [index0, index1, index2,
      h0, h1, ht, h2, hl, hh0, hh, bind_tc_ok]
  · apply Prod.ext
    · simpa only [AspisR1.TerminalV4QM31MulCurrent.mulWords,
      AspisR1.TerminalV4TowerAdd.wordsCM, AspisR1.TerminalV4QM31MulCurrent.P,
      AspisR1.TerminalV4TowerAdd.P, AspisR1.TerminalV4M31AddSub.P,
      hv0, hv1] using hvl
    · simpa only [AspisR1.TerminalV4QM31MulCurrent.mulWords,
      AspisR1.TerminalV4TowerAdd.wordsCM, AspisR1.TerminalV4QM31MulCurrent.P,
      AspisR1.TerminalV4TowerAdd.P, AspisR1.TerminalV4M31AddSub.P,
      hvh0, hv2', hv0, hv1] using hvh

private theorem component_eq_mul (a : Component) (x y : CM)
    (hx : CanonicalCM x) (hy : CanonicalCM y) (hp : ComponentFor a x) :
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a, y) = field.CM31.mul x y := by
  obtain ⟨z, hz, _, hv⟩ := current_component_mul_words a x y hx hy hp
  obtain ⟨w, hw, _, hwa, hwb⟩ :=
    AspisR1.TerminalV4CM31MulCurrent.current_mul_words x y hx hy
  have hwv : (w.a.val, w.b.val) = AspisR1.TerminalV4QM31MulCurrent.mulWords
      (AspisR1.TerminalV4TowerAdd.wordsCM x)
      (AspisR1.TerminalV4TowerAdd.wordsCM y) := Prod.ext hwa hwb
  have hzw := cm_eq_of_words z w (hv.trans hwv.symm)
  rw [hz, hw, hzw]

theorem prepared_mul_eq (p : Prepared) (x y : QM)
    (hx : CanonicalQM x) (hy : CanonicalQM y) (hp : PreparedFor p x) :
    field.PreparedQm31Multiplier.mul p y = field.QM31.mul x y := by
  obtain ⟨t, a, b, c, ht, hct, ha, hb, hc, harr⟩ := hp
  obtain ⟨s, hs, hcs, _, _⟩ :=
    AspisR1.TerminalV4TowerAdd.current_cm_add_mod y.c0 y.c1 hy.1 hy.2
  have hpa := component_eq_mul a x.c0 y.c0 hx.1 hy.1 ha
  have hpb := component_eq_mul b x.c1 y.c1 hx.2 hy.2 hb
  have hpc := component_eq_mul c t s hct hcs hc
  simp only [field.PreparedQm31Multiplier.mul, harr,
    componentIndex0,
    componentIndex1,
    componentIndex2,
    hpa, hpb, hs, hpc, bind_tc_ok, field.QM31.mul, ht]

theorem prepared_mul_exact (p : Prepared) (x y : QM)
    (hx : CanonicalQM x) (hy : CanonicalQM y) (hp : PreparedFor p x) :
    ∃ z : QM, field.PreparedQm31Multiplier.mul p y = .ok z ∧
      CanonicalQM z ∧ AspisR1.TerminalV4QM31TowerCurrent.decode z =
        AspisR1.TerminalV4QM31TowerCurrent.decode x * AspisR1.TerminalV4QM31TowerCurrent.decode y := by
  rw [prepared_mul_eq p x y hx hy hp]
  exact AspisR1.TerminalV4QM31TowerCurrent.current_qm_mul_exact x y hx hy

#print axioms current_component_mul_words
#print axioms prepared_mul_eq
#print axioms prepared_mul_exact
end AspisR1.TerminalV4PreparedMulExactCurrent
