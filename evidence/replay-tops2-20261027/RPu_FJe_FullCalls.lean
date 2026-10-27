import RPu_FJe_FinalConstants
import RPu_FJe_ThreeColumns
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_FullCalls
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FJb_MatrixGroupStep (State)
/-- Exact same-call operands,with the six original table reads identified.
No success or VALUE of an independently selected subcall is assumed. -/
theorem value (s l : State) (out : Array NQ 4#usize)
    (run : state_only_poseidon.interpolated_full_pair_packed s l=ok out) :
    ∃ (q0 q1 q2 : NQ) (even odd middle : State),
      Array.index_usize l 1#usize=ok q0 ∧
      Array.index_usize l 9#usize=ok q1 ∧
      Array.index_usize l 10#usize=ok q2 ∧
      state_only_poseidon.interpolate_three_constant_columns
        (Array.make 3#usize [q0,q1,q2]) (FJb_InitialConstants.row 2)
        (FJe_FinalConstants.row 0) (FJe_FinalConstants.row 2)=ok even ∧
      state_only_poseidon.interpolate_three_constant_columns
        (Array.make 3#usize [q0,q1,q2]) (FJb_InitialConstants.row 3)
        (FJe_FinalConstants.row 1) (FJe_FinalConstants.row 3)=ok odd ∧
      state_only_poseidon.full_round s even=ok middle ∧
      state_only_poseidon.full_round_packed middle odd=ok out := by
  unfold state_only_poseidon.interpolated_full_pair_packed at run
  obtain ⟨q0,r0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q1,r1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨q2,r2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨a0,ra0,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨a1,ra1,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨a2,ra2,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨even,re,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨a3,ra3,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨a4,ra4,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨a5,ra5,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨odd,ro,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨middle,rm,tail⟩ := FIv_Map.bind_success _ _ _ run
  have e0 : a0=FJb_InitialConstants.row 2 := Result.ok.inj
    (ra0.symm.trans (FJb_InitialConstants.read 2#usize (by decide)))
  have e1 : a1=FJe_FinalConstants.row 0 := Result.ok.inj
    (ra1.symm.trans (FJe_FinalConstants.read 0#usize (by decide)))
  have e2 : a2=FJe_FinalConstants.row 2 := Result.ok.inj
    (ra2.symm.trans (FJe_FinalConstants.read 2#usize (by decide)))
  have e3 : a3=FJb_InitialConstants.row 3 := Result.ok.inj
    (ra3.symm.trans (FJb_InitialConstants.read 3#usize (by decide)))
  have e4 : a4=FJe_FinalConstants.row 1 := Result.ok.inj
    (ra4.symm.trans (FJe_FinalConstants.read 1#usize (by decide)))
  have e5 : a5=FJe_FinalConstants.row 3 := Result.ok.inj
    (ra5.symm.trans (FJe_FinalConstants.read 3#usize (by decide)))
  subst a0;subst a1;subst a2;subst a3;subst a4;subst a5
  exact ⟨q0,q1,q2,even,odd,middle,r0,r1,r2,re,ro,rm,tail⟩
#print axioms value
end AspisR1.FJe_FullCalls
end
