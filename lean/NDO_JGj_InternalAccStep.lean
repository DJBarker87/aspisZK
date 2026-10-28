import NDO_JGj_RawBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalAccStep
open Aeneas Aeneas.Std Result WP FIq_Native
open JGj_RawBounds
def step (a : Raw) (w : Words) (i : Usize) : Result Raw := do
  let x ← Array.index_usize w i
  let y ← Array.index_usize a i
  let z ← y+FJb_WideSum4.wide x
  Array.update a i z
theorem source (a : Raw) (w : Words) (i : Usize) (n : Nat)
    (hi : i.val<(4#usize).val) (hn : n≤80) (ha : Bound a (n*P)) (hw : Canonical w) :
    ∃ out,step a w i=ok out ∧ Bound out ((n+1)*P) := by
  let x := FJb_TailCell.cell w ⟨i.val,hi⟩
  let y := FJb_TailCell.cell a ⟨i.val,hi⟩
  have rx : Array.index_usize w i=ok x := RawPoseidonExternalRowReads.array_index_usize_ok w i hi
  have ry : Array.index_usize a i=ok y := RawPoseidonExternalRowReads.array_index_usize_ok a i hi
  have bx : x.val<P := hw _
  have by0 : y.val<n*P := ha _
  have limit : 81*P<2^64 := by norm_num [P,AspisV8R17.RawReducer.P]
  have prod : n*P≤80*P := Nat.mul_le_mul_right P hn
  have safe : y.val+(FJb_WideSum4.wide x).val<2^64 := by rw [FJb_WideSum4.wide_val];omega
  obtain ⟨z,rz,vz⟩ := ExtractedMaskReducerOps.add_success y (FJb_WideSum4.wide x) safe
  rw [FJb_WideSum4.wide_val] at vz
  obtain ⟨out,ro,vo⟩ := WP.spec_imp_exists (Array.update_spec a i z (by simpa only [a.property] using hi))
  have bz : z.val<(n+1)*P := by rw [vz,Nat.add_mul,Nat.one_mul];omega
  have ba : Bound a ((n+1)*P) := by
    intro j
    have hj := ha j
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
  have rzNative : (y+FJb_WideSum4.wide x : Result U64)=ok z := rz
  exact ⟨out,by simp only [step,rx,ry,rzNative,ro,bind_tc_ok],vo ▸ JGj_RawBounds.update a _ i z hi ba bz⟩
theorem unfold_loop (a : Raw) (w : Words) (i : Usize) :
    state_only_poseidon.internal_linear_lazy_loop0_loop0 a w i=
      (if i<4#usize then do
        let next ← step a w i
        let i1 ← i+1#usize
        state_only_poseidon.internal_linear_lazy_loop0_loop0 next w i1
      else ok a) := by
  rw [state_only_poseidon.internal_linear_lazy_loop0_loop0.eq_def]
  simp only [step,lift,bind_tc_ok,bind_assoc_eq,FJb_WideSum4.wide]
#print axioms source
#print axioms unfold_loop
end AspisR1.JGj_InternalAccStep
end
