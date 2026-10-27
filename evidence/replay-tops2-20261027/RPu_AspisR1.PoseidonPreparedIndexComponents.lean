import RPu_AspisR1.PoseidonPreparedIndexLoopStep
import ExtractedMaskPreparedState

set_option autoImplicit false
namespace AspisR1PoseidonPreparedIndexComponents
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd

abbrev QM := field.QM31
abbrev CM := field.CM31
abbrev M31 := field.M31
abbrev Components := Array (Array M31 3#usize) 3#usize

theorem actual_components_success (q : QM) (hq : CanonicalQM q) :
  ∃ components : Components,
    (do
      let rightSum ← field.CM31.add q.c0 q.c1
      let m ← field.M31.add q.c0.a q.c0.b
      let m1 ← field.M31.add q.c1.a q.c1.b
      let m2 ← field.M31.add rightSum.a rightSum.b
      ok (Array.make 3#usize [
        (Array.make 3#usize [q.c0.a, q.c0.b, m] : Array M31 3#usize),
        (Array.make 3#usize [q.c1.a, q.c1.b, m1] : Array M31 3#usize),
        (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array M31 3#usize)] : Components)) = .ok components := by
  obtain ⟨rightSum, hsum, hsumCan, _, _⟩ := current_cm_add_mod q.c0 q.c1 hq.1 hq.2
  obtain ⟨m, hm, _, _⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c0.a q.c0.b hq.1.1 hq.1.2
  obtain ⟨m1, hm1, _, _⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c1.a q.c1.b hq.2.1 hq.2.2
  obtain ⟨m2, hm2, _, _⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod rightSum.a rightSum.b hsumCan.1 hsumCan.2
  let built : Components := Array.make 3#usize [
    (Array.make 3#usize [q.c0.a, q.c0.b, m] : Array M31 3#usize),
    (Array.make 3#usize [q.c1.a, q.c1.b, m1] : Array M31 3#usize),
    (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array M31 3#usize)]
  refine ⟨built, ?_⟩
  simp only [hsum, hm, hm1, hm2, bind_tc_ok, built]

#print axioms actual_components_success
end AspisR1PoseidonPreparedIndexComponents
