import Aeneas
import PoseidonExternalLazySourceCut
import AspisR1.PoseidonExternalRowExtensionMap

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1.PoseidonExternalLinearGroupStep
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalRowExtensionMap

abbrev QM := field.QM31
abbrev State := Array QM 16#usize

private theorem update_success (a : State) (i : Usize) (x : QM)
    (hi : i.val < 16) :
    ∃ out : State, Array.update a i x = .ok out ∧ out = a.set i x := by
  obtain ⟨out, hr, hs⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa [a.property] using hi))
  exact ⟨out, hr, hs⟩

/-- The source continuation for one external-linear group, after its four
successful state reads. It consumes the actual extension-limb `Array.map`,
the four generated row calls, and four checked in-place updates. The read
equations are explicit so the loop invariant can instantiate them from its
checked index operations without introducing a model premise. -/
theorem group_step_after_reads
    (state : State) (q0 q1 q2 q3 : QM) (i0 i1 i2 i3 : Usize)
    (hread0 : Array.index_usize state i0 = .ok q0)
    (hread1 : Array.index_usize state i1 = .ok q1)
    (hread2 : Array.index_usize state i2 = .ok q2)
    (hread3 : Array.index_usize state i3 = .ok q3)
    (hi0 : i0.val < 16) (hi1 : i1.val < 16)
    (hi2 : i2.val < 16) (hi3 : i3.val < 16) :
    ∃ v0 v1 v2 v3 : QM, ∃ s1 s2 s3 s4 : State,
      state_only_poseidon.external_linear_lazy_row
        (groupWords q0 q1 q2 q3) 0#usize = .ok v0 ∧
      state_only_poseidon.external_linear_lazy_row
        (groupWords q0 q1 q2 q3) 1#usize = .ok v1 ∧
      state_only_poseidon.external_linear_lazy_row
        (groupWords q0 q1 q2 q3) 2#usize = .ok v2 ∧
      state_only_poseidon.external_linear_lazy_row
        (groupWords q0 q1 q2 q3) 3#usize = .ok v3 ∧
      (do
        let x0 ← Array.index_usize state i0
        let x1 ← Array.index_usize state i1
        let x2 ← Array.index_usize state i2
        let x3 ← Array.index_usize state i3
        let input ← core.array.Array.map
          (BuiltinFnMut QM (Array Std.U32 4#usize))
          (Array.make 4#usize [x0,x1,x2,x3])
          state_only_poseidon.extension_limbs
        let o0 ← state_only_poseidon.external_linear_lazy_row input 0#usize
        let a0 ← Array.update state i0 o0
        let o1 ← state_only_poseidon.external_linear_lazy_row input 1#usize
        let a1 ← Array.update a0 i1 o1
        let o2 ← state_only_poseidon.external_linear_lazy_row input 2#usize
        let a2 ← Array.update a1 i2 o2
        let o3 ← state_only_poseidon.external_linear_lazy_row input 3#usize
        Array.update a2 i3 o3) = .ok s4 ∧
      s1 = state.set i0 v0 ∧ s2 = s1.set i1 v1 ∧
      s3 = s2.set i2 v2 ∧ s4 = s3.set i3 v3 := by
  have hmap := group_extension_limbs_map q0 q1 q2 q3
  have hmap' : core.array.Array.map
      (BuiltinFnMut QM (Array Std.U32 4#usize))
      (Array.make 4#usize [q0,q1,q2,q3])
      state_only_poseidon.extension_limbs = .ok (groupWords q0 q1 q2 q3) := by
    simpa only [groupInput] using hmap
  obtain ⟨v0, hv0, _, _⟩ := group_row_success q0 q1 q2 q3 0#usize (by decide)
  obtain ⟨v1, hv1, _, _⟩ := group_row_success q0 q1 q2 q3 1#usize (by decide)
  obtain ⟨v2, hv2, _, _⟩ := group_row_success q0 q1 q2 q3 2#usize (by decide)
  obtain ⟨v3, hv3, _, _⟩ := group_row_success q0 q1 q2 q3 3#usize (by decide)
  obtain ⟨s1, hs1, hs1set⟩ := update_success state i0 v0 hi0
  obtain ⟨s2, hs2, hs2set⟩ := update_success s1 i1 v1 hi1
  obtain ⟨s3, hs3, hs3set⟩ := update_success s2 i2 v2 hi2
  obtain ⟨s4, hs4, hs4set⟩ := update_success s3 i3 v3 hi3
  refine ⟨v0,v1,v2,v3,s1,s2,s3,s4,hv0,hv1,hv2,hv3,?_,hs1set,hs2set,hs3set,hs4set⟩
  simp only [hread0, hread1, hread2, hread3, hmap',
    hv0, hs1, hv1, hs2, hv2, hs3, hv3, hs4,
    bind_tc_ok]

#print axioms group_step_after_reads
end AspisR1.PoseidonExternalLinearGroupStep
