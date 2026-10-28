import R1Z.PV_RDB2C_PV_B2_F_OriginalMutation
set_option autoImplicit false
namespace PV_B2_F_AllocationTransport
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
abbrev RustResult := core.result.Result Out verifier.Error

def zeros : Out := Array.repeat 1024#usize aspis_core.field.wide_exact.WideExact.ZERO

/-- One named fallible allocation request. The actual OS outcome remains a
native P obligation; these laws quantify over both outcomes. -/
inductive Outcome where
  | supplied
  | denied

def copied (event : Outcome) (w : host_weights.Weights) (kappa : E) : Result RustResult :=
  match event with
  | .denied => ok (.Err verifier.Error.Allocation)
  | .supplied => do
    let (_,updated) ← pv_b2_materialize w kappa zeros
    ok (.Ok updated)

def original (event : Outcome) (w : host_weights.Weights) (kappa : E) : Result RustResult :=
  match event with
  | .denied => ok (.Err verifier.Error.Allocation)
  | .supplied => do
    let k ← host_weights.powers7 kappa
    let updated ← PV_B2_F_OriginalMutation.remaining w k 1024 0#usize zeros
    ok (.Ok updated)

theorem zero_suffix : PV_B2_F_ArrayMutation.ZeroSuffix zeros 0 := by
  intro i _ hi
  change (List.replicate 1024 aspis_core.field.wide_exact.WideExact.ZERO)[i]? = _
  rw [List.getElem?_replicate,if_pos hi]

theorem equal (event : Outcome) (w : host_weights.Weights) (kappa : E) :
    copied event w kappa = original event w kappa := by
  cases event with
  | denied => rfl
  | supplied =>
    obtain ⟨k,hk⟩ := PV_B2_C_Powers7Total.source kappa
    have hm := PV_B2_F_OriginalMutation.loop w k zeros 0#usize zero_suffix
    simp only [show (0#usize).val=0 from by scalar_tac,Nat.sub_zero] at hm
    have hc := PV_B2_F_MutationModel.source w kappa zeros
    unfold copied original
    simp only [pv_b2_materialize,host_weights.Weights.materialize,hc,
      PV_B2_F_MutationModel.values,hk,bind_tc_ok]
    rw [hm]
    simp only [bind_assoc,bind_tc_ok]
    rfl

theorem denied (w : host_weights.Weights) (kappa : E) :
    copied .denied w kappa = ok (.Err verifier.Error.Allocation) := rfl

theorem supplied (w : host_weights.Weights) (kappa : E) :
    ∃ out, copied .supplied w kappa = ok (.Ok out) := by
  obtain ⟨out,ho⟩ := PV_B2_D_MaterializeTotal.source w kappa zeros
  exact ⟨out,by simp only [copied,ho,bind_tc_ok]; rfl⟩
#print axioms zero_suffix
#print axioms equal
#print axioms denied
#print axioms supplied
end PV_B2_F_AllocationTransport
