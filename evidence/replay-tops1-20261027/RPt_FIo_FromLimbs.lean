import RPt_FIo_Constants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_FromLimbs
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem canonical (limbs : Array U32 8#usize) (z : NE)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs limbs=ok (some z)) :
    FIo_WideValues.Canon z := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs at run
  simp only [FIo_Native.aspis_core.field.P] at run
  obtain ⟨v0,hv0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i h0
  obtain ⟨v1,hv1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i h1
  obtain ⟨v2,hv2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i h2
  obtain ⟨v3,hv3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i h3
  obtain ⟨v4,hv4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i h4
  obtain ⟨v5,hv5,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i h5
  obtain ⟨v6,hv6,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i h6
  obtain ⟨v7,hv7,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  split at run
  · cases run
  rename_i h7
  have same : (⟨⟨⟨v0,v1⟩,⟨v2,v3⟩⟩,⟨⟨v4,v5⟩,⟨v6,v7⟩⟩⟩ : NE)=z := Option.some.inj (Result.ok.inj run)
  subst z
  change ((v0.val<2147483647 ∧ v1.val<2147483647) ∧
    (v2.val<2147483647 ∧ v3.val<2147483647)) ∧
    ((v4.val<2147483647 ∧ v5.val<2147483647) ∧
    (v6.val<2147483647 ∧ v7.val<2147483647))
  scalar_tac

#print axioms canonical
end AspisR1.FIo_FromLimbs
end
