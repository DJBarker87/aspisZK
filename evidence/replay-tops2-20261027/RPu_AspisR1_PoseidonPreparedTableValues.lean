import RPu_AspisR1_PoseidonPreparedIndexComponentsCanonical
import RPu_PoseidonPreparedSum3Source

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedTableValues
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd AspisR1PoseidonPreparedSum3Source

abbrev QM := field.QM31
abbrev CM := field.CM31
abbrev M31 := field.M31
abbrev Components := Array (Array M31 3#usize) 3#usize
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev P : Nat := 2147483647

theorem actual_components_values (q : QM) (hq : CanonicalQM q) :
    ∃ rightSum m0 m1 m2 components,
      field.CM31.add q.c0 q.c1 = .ok rightSum ∧
      field.M31.add q.c0.a q.c0.b = .ok m0 ∧
      field.M31.add q.c1.a q.c1.b = .ok m1 ∧
      field.M31.add rightSum.a rightSum.b = .ok m2 ∧
      m0.val = (q.c0.a.val + q.c0.b.val) % P ∧
      m1.val = (q.c1.a.val + q.c1.b.val) % P ∧
      m2.val = (rightSum.a.val + rightSum.b.val) % P ∧
      (do
        let sum ← field.CM31.add q.c0 q.c1
        let a ← field.M31.add q.c0.a q.c0.b
        let b ← field.M31.add q.c1.a q.c1.b
        let c ← field.M31.add sum.a sum.b
        ok (Array.make 3#usize [
          (Array.make 3#usize [q.c0.a,q.c0.b,a] : Array M31 3#usize),
          (Array.make 3#usize [q.c1.a,q.c1.b,b] : Array M31 3#usize),
          (Array.make 3#usize [sum.a,sum.b,c] : Array M31 3#usize)] : Components)) = .ok components ∧
      components = Array.make 3#usize [
        (Array.make 3#usize [q.c0.a,q.c0.b,m0] : Array M31 3#usize),
        (Array.make 3#usize [q.c1.a,q.c1.b,m1] : Array M31 3#usize),
        (Array.make 3#usize [rightSum.a,rightSum.b,m2] : Array M31 3#usize)] := by
  obtain ⟨components,hsource⟩ := AspisR1PoseidonPreparedIndexComponents.actual_components_success q hq
  obtain ⟨rightSum,hsum,hsumCan,hrsa,hrsb⟩ :=
    AspisR1.ExtractedMaskTowerAdd.current_cm_add_mod q.c0 q.c1 hq.1 hq.2
  obtain ⟨m0,hm0,hv0,hcan0⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c0.a q.c0.b hq.1.1 hq.1.2
  obtain ⟨m1,hm1,hv1,hcan1⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod q.c1.a q.c1.b hq.2.1 hq.2.2
  obtain ⟨m2,hm2,hv2,hcan2⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod rightSum.a rightSum.b hsumCan.1 hsumCan.2
  let built : Components := Array.make 3#usize [
    (Array.make 3#usize [q.c0.a,q.c0.b,m0] : Array M31 3#usize),
    (Array.make 3#usize [q.c1.a,q.c1.b,m1] : Array M31 3#usize),
    (Array.make 3#usize [rightSum.a,rightSum.b,m2] : Array M31 3#usize)]
  have hbuilt : (do
      let sum ← field.CM31.add q.c0 q.c1
      let a ← field.M31.add q.c0.a q.c0.b
      let b ← field.M31.add q.c1.a q.c1.b
      let c ← field.M31.add sum.a sum.b
      ok (Array.make 3#usize [
        (Array.make 3#usize [q.c0.a,q.c0.b,a] : Array M31 3#usize),
        (Array.make 3#usize [q.c1.a,q.c1.b,b] : Array M31 3#usize),
        (Array.make 3#usize [sum.a,sum.b,c] : Array M31 3#usize)] : Components)) = .ok built := by
    simp only [hsum, hm0, hm1, hm2, bind_tc_ok, built]
  have hcomponents : components = built := Result.ok.inj (hsource.symm.trans hbuilt)
  exact ⟨rightSum,m0,m1,m2,components,hsum,hm0,hm1,hm2,hv0,hv1,hv2,hsource,hcomponents⟩

#print axioms actual_components_values
end AspisR1.PoseidonPreparedTableValues
