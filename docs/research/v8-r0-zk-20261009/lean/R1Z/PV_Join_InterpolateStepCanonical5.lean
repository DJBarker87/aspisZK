import R1Z.PV_Join_AccumulateLoopCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_InterpolateStepCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5 PV_Join_ResultInvariant5
open PV_Join_AccumulateCanonical5
variable [ExternalTypes]

theorem step (ops : ExternalFuns) (values out : QA) (i : Usize) (hout : QArray out) :
    Safe (fun cf => match cf with
      | .done ys => QArray ys
      | .cont ys => inv ys ∧ rank ys < rank (out,i))
      (@host_sumcheck.interpolate_loop.body _ (ProverRwP6BodyStore.selected ops) values out i) := by
  unfold host_sumcheck.interpolate_loop.body
  split
  · rename_i hi
    intro cf hcf
    obtain ⟨pair,hpair,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    rcases pair with ⟨basis,denominator⟩
    obtain ⟨q,hq,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    obtain ⟨m,hm,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    obtain ⟨scale,hscale,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    obtain ⟨ys,hys,hcf⟩ := PV_Join_BindSuccess5.unpack _ _ _ hcf
    have hy := PV_Join_AccumulateLoopCanonical5.accumulate ops out basis scale hout ys hys
    simp only [lift,bind_tc_ok] at hcf
    cases hcf
    refine ⟨hy,?_⟩
    have hval : (Std.Usize.wrapping_add i 1#usize).val = i.val+1 := by
      rw [Std.Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize = i.val+1
      apply Nat.mod_eq_of_lt
      have hbound : i.val<28 := hi
      have big := (28#usize).hSize
      change 28 < UScalar.size .Usize at big
      omega
    change 28-(Std.Usize.wrapping_add i 1#usize).val < 28-i.val
    rw [hval]
    have hbound : i.val<28 := hi
    omega
  · exact PV_Join_ResultInvariant5.ok _ _ hout

#print axioms step
end R1Z.PV_Join_InterpolateStepCanonical5
