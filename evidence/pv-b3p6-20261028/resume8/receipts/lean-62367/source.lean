import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev DigestQ := Array aspis_core.field.QM31 8#usize
abbrev DigestM := Array U32 8#usize
abbrev FrontierM := Array DigestM 20#usize

/-- A continuation rule for the emitted optional-recipient join point. -/
theorem recipient_continue8 {β : Type} (recipient : Option DigestM) (output : DigestQ)
    (opened : Array aspis_core.field.QM31 16#usize) (selectors : reference_copy_terminal.Selectors)
    (f : DigestQ → Result β) (hf : ∀ next, Success (f next)) :
    Success (match (generalizing := false) recipient with
    | none => f output
    | some expected => do
      let base ← lift (Usize.wrapping_mul 29#usize 16#usize)
      let row ← lift (Usize.wrapping_add base 11#usize)
      let selector ← reference_copy_terminal.Selectors.row selectors row
      let next ← reference_terminal.add_digest_binding output selector opened 0#usize expected false
      f next) := by
  cases recipient with
  | none => exact hf output
  | some expected =>
    apply lift_total
    apply lift_total
    apply bind
    · apply row_total
      apply row_address_bound <;> scalar_tac
    intro selector
    apply bind
    · apply total_reference_terminal_add_digest_binding <;> scalar_tac
    intro next
    exact hf next

/-- Both branches of one actual public-frontier level feed the same
continuation. Roots remain symbolic table entries. -/
theorem frontier_continue8 {β : Type} (output : DigestQ) (opened : Array aspis_core.field.QM31 16#usize)
    (selectors : reference_copy_terminal.Selectors) (frontier : FrontierM)
    (level block : Usize) (bit : U64) (f : DigestQ → Result β)
    (hl : level.val<20) (hb : block.val<64) (hf : ∀ next, Success (f next)) :
    Success (if bit=0#u64 then do
      let row ← lift (Usize.wrapping_mul block 16#usize)
      let selector ← reference_copy_terminal.Selectors.row selectors row
      let expected ← reference_terminal.empty_root level
      let next ← reference_terminal.add_digest_binding output selector opened aspis_statement.poseidon2.RATE expected true
      f next
    else do
      let base ← lift (Usize.wrapping_mul block 16#usize)
      let row ← lift (Usize.wrapping_add base 12#usize)
      let selector ← reference_copy_terminal.Selectors.row selectors row
      let expected ← reference_terminal.digest227 frontier level
      let next ← reference_terminal.add_digest_binding output selector opened 0#usize expected false
      f next) := by
  split
  · apply lift_total
    apply bind
    · exact row_total selectors _ (row_mul_bound block hb)
    intro selector
    apply bind
    · exact empty_root_total level (by omega)
    intro expected
    apply bind
    · apply total_reference_terminal_add_digest_binding
      unfold aspis_statement.poseidon2.RATE
      change 8≤8
      omega
    intro next
    exact hf next
  · apply lift_total
    apply lift_total
    apply bind
    · exact row_total selectors _ (row_address_bound block 12#usize hb (by scalar_tac))
    intro selector
    apply bind
    · exact digest_total frontier level hl
    intro expected
    apply bind
    · apply total_reference_terminal_add_digest_binding <;> scalar_tac
    intro next
    exact hf next

#print axioms recipient_continue8
#print axioms frontier_continue8

/-- Eliminate only the head successful join, leaving the continuation opaque. -/
theorem digest_ok_continue8 {α β : Type} (x : α) (f : α → Result β)
    (h : Success (f x)) : Success (Result.ok x >>= f) := h
#print axioms digest_ok_continue8
end PV_B3P_Success227
