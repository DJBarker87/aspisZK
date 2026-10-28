import NDO_JGj_RawBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalShift
open Aeneas Aeneas.Std Result WP FIq_Native
open JGj_RawBounds
theorem word (x : U32) (s : U8) (hx : x.val<P) (hs : s.val≤16) :
    ∃ out,(FJb_WideSum4.wide x <<< s : Result U64)=ok out ∧ out.val<2^47 := by
  have hp : 2^s.val≤2^16 := Nat.pow_le_pow_right (by decide) hs
  have hx31 : x.val<2^31 := by norm_num [P,AspisV8R17.RawReducer.P] at hx ⊢;omega
  have prod : x.val*2^s.val<2^47 := by
    calc
      x.val*2^s.val≤x.val*2^16 := Nat.mul_le_mul_left _ hp
      _ < (2^31)*2^16 := Nat.mul_lt_mul_of_pos_right hx31 (by decide)
      _ = 2^47 := by norm_num
  obtain ⟨out,ro,vo,_⟩ := WP.spec_imp_exists (U64.ShiftLeft_spec (FJb_WideSum4.wide x) s (by omega))
  rw [Nat.shiftLeft_eq,U64.size,U64.numBits] at vo
  change out.val=((FJb_WideSum4.wide x).val*2^s.val)%2^64 at vo
  rw [FJb_WideSum4.wide_val,Nat.mod_eq_of_lt (by omega)] at vo
  exact ⟨out,ro,by rw [vo];exact prod⟩
theorem read (lane : Usize) (hl : 1≤lane.val) (hh : lane.val<16) :
    ∃ delta shift,(lane-1#usize : Result Usize)=ok delta ∧
      Array.index_usize state_only_poseidon.internal_linear_lazy.SHIFTS delta=ok shift ∧ shift.val≤16 := by
  have spec : (lane-1#usize : Result Usize) ⦃ d=>d.val=lane.val-(1#usize).val ∧ (1#usize).val≤lane.val ⦄ := by
    apply UScalar.sub_spec
    scalar_tac
  obtain ⟨delta,rd,vd,_⟩ := WP.spec_imp_exists spec
  have vone : (1#usize).val=1 := rfl
  rw [vone] at vd
  have hd : delta.val<(15#usize).val := by change delta.val<15;omega
  let shift := FJb_TailCell.cell state_only_poseidon.internal_linear_lazy.SHIFTS ⟨delta.val,hd⟩
  have rs : Array.index_usize state_only_poseidon.internal_linear_lazy.SHIFTS delta=ok shift :=
    RawPoseidonExternalRowReads.array_index_usize_ok _ delta hd
  have all : ∀ x∈state_only_poseidon.internal_linear_lazy.SHIFTS.val,x.val≤16 := by
    intro x hx
    simp only [state_only_poseidon.internal_linear_lazy.SHIFTS,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact ⟨delta,shift,rd,rs,all shift (List.getElem_mem _)⟩
#print axioms word
#print axioms read
end AspisR1.JGj_InternalShift
end
