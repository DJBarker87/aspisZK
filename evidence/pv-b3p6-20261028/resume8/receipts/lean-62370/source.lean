import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- Successful Rust Ok, distinct from success of the extraction Result alone. -/
def RustOk {α ε : Type} (r : Result (core.result.Result α ε)) : Prop :=
  ∃ value, r = .ok (.Ok value)

theorem rust_ok {α ε : Type} (x : α) : RustOk ((.ok (.Ok x)) : Result (core.result.Result α ε)) :=
  ⟨x,rfl⟩

theorem rust_bind {α β ε : Type} (r : Result α)
    (f : α → Result (core.result.Result β ε))
    (hr : Success r) (hf : ∀ x, RustOk (f x)) : RustOk (r >>= f) := by
  obtain ⟨x,hx⟩ := hr
  rw [hx]
  exact hf x

theorem rust_lift {α β ε : Type} (x : α)
    (f : α → Result (core.result.Result β ε))
    (hf : RustOk (f x)) : RustOk (lift x >>= f) := hf

theorem digest_field_withdrawal (p : reference_terminal.SemanticPublic) :
    (valid_public p).withdrawal_amount = none := rfl

theorem valid_public_reset (p : reference_terminal.SemanticPublic) :
    {valid_public p with withdrawal_amount := none} = valid_public p := rfl

theorem selected_h1_column_value : reference_terminal.SELECTED_H1_COLUMN = .ok 26#usize := by
  unfold reference_terminal.SELECTED_H1_COLUMN
    reference_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    aspis_core.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  exact checked_add_exact _ _ _ (by rfl)

theorem selected_g_column_value : reference_terminal.SELECTED_G_COLUMN = .ok 27#usize := by
  unfold reference_terminal.SELECTED_G_COLUMN
  rw [selected_h1_column_value]
  exact checked_add_exact _ _ _ (by rfl)

#print axioms rust_ok
#print axioms rust_bind
#print axioms rust_lift
#print axioms digest_field_withdrawal
#print axioms valid_public_reset
#print axioms selected_h1_column_value
#print axioms selected_g_column_value
end PV_B3P_Success227
