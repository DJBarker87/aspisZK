import AspisR1.PoseidonPreparedIndexLoopStep
import AspisR1.PoseidonPreparedIndexComponents
import ExtractedMaskPreparedState

set_option autoImplicit false
namespace AspisR1PoseidonPreparedIndexComponentsCanonical
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd

abbrev QM := field.QM31
abbrev CM := field.CM31
abbrev M31 := field.M31
abbrev Components := Array (Array M31 3#usize) 3#usize

theorem actual_components_canonical (q : QM) (hq : CanonicalQM q) :
    ∃ components : Components,
      (do
        let rightSum ← field.CM31.add q.c0 q.c1
        let m ← field.M31.add q.c0.a q.c0.b
        let m1 ← field.M31.add q.c1.a q.c1.b
        let m2 ← field.M31.add rightSum.a rightSum.b
        ok (Array.make 3#usize [
          (Array.make 3#usize [q.c0.a, q.c0.b, m] : Array M31 3#usize),
          (Array.make 3#usize [q.c1.a, q.c1.b, m1] : Array M31 3#usize),
          (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array M31 3#usize)] : Components)) = .ok components ∧
      (∀ (c ch : Std.Usize) (hc : c.val < 3) (hch : ch.val < 3),
        (AspisR1PoseidonPreparedChannelRunStepLocal.at3
          (AspisR1PoseidonPreparedChannelRunStepLocal.at3 components c hc) ch hch).val < P) := by
  obtain ⟨components, hrun⟩ := AspisR1PoseidonPreparedIndexComponents.actual_components_success q hq
  obtain ⟨rightSum, hsum, hsumCan, _, _⟩ := current_cm_add_mod q.c0 q.c1 hq.1 hq.2
  obtain ⟨m, hm, _, hmCan⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c0.a q.c0.b hq.1.1 hq.1.2
  obtain ⟨m1, hm1, _, hm1Can⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c1.a q.c1.b hq.2.1 hq.2.2
  obtain ⟨m2, hm2, _, hm2Can⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod rightSum.a rightSum.b hsumCan.1 hsumCan.2
  let built : Components := Array.make 3#usize [
    (Array.make 3#usize [q.c0.a, q.c0.b, m] : Array M31 3#usize),
    (Array.make 3#usize [q.c1.a, q.c1.b, m1] : Array M31 3#usize),
    (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array M31 3#usize)]
  have hb : components = built := by
    have hrun' := hrun
    simp only [hsum, hm, hm1, hm2, bind_tc_ok, built] at hrun'
    exact (Result.ok.inj hrun').symm
  refine ⟨components, hrun, ?_⟩
  intro c ch hc hch
  have hcCases : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
  have hchCases : ch.val = 0 ∨ ch.val = 1 ∨ ch.val = 2 := by omega
  rcases hcCases with hc0 | hc1 | hc2
  · have : c = 0#usize := UScalar.eq_of_val_eq hc0
    subst c
    rcases hchCases with h0 | h1 | h2
    · have : ch = 0#usize := UScalar.eq_of_val_eq h0
      subst ch
      simpa [AspisR1PoseidonPreparedChannelRunStepLocal.at3, hb, built, Array.make] using hq.1.1
    · have : ch = 1#usize := UScalar.eq_of_val_eq h1
      subst ch
      simpa [AspisR1PoseidonPreparedChannelRunStepLocal.at3, hb, built, Array.make] using hq.1.2
    · have : ch = 2#usize := UScalar.eq_of_val_eq h2
      subst ch
      simpa [AspisR1PoseidonPreparedChannelRunStepLocal.at3, hb, built, Array.make] using hmCan
  · have : c = 1#usize := UScalar.eq_of_val_eq hc1
    subst c
    rcases hchCases with h0 | h1 | h2
    · have : ch = 0#usize := UScalar.eq_of_val_eq h0
      subst ch
      simpa [AspisR1PoseidonPreparedChannelRunStepLocal.at3, hb, built, Array.make] using hq.2.1
    · have : ch = 1#usize := UScalar.eq_of_val_eq h1
      subst ch
      simpa [AspisR1PoseidonPreparedChannelRunStepLocal.at3, hb, built, Array.make] using hq.2.2
    · have : ch = 2#usize := UScalar.eq_of_val_eq h2
      subst ch
      simpa [AspisR1PoseidonPreparedChannelRunStepLocal.at3, hb, built, Array.make] using hm1Can
  · have : c = 2#usize := UScalar.eq_of_val_eq hc2
    subst c
    rcases hchCases with h0 | h1 | h2
    · have : ch = 0#usize := UScalar.eq_of_val_eq h0
      subst ch
      simpa [AspisR1PoseidonPreparedChannelRunStepLocal.at3, hb, built, Array.make] using hsumCan.1
    · have : ch = 1#usize := UScalar.eq_of_val_eq h1
      subst ch
      simpa [AspisR1PoseidonPreparedChannelRunStepLocal.at3, hb, built, Array.make] using hsumCan.2
    · have : ch = 2#usize := UScalar.eq_of_val_eq h2
      subst ch
      simpa [AspisR1PoseidonPreparedChannelRunStepLocal.at3, hb, built, Array.make] using hm2Can

#print axioms actual_components_canonical
end AspisR1PoseidonPreparedIndexComponentsCanonical
