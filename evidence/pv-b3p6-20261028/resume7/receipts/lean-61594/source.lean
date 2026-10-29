import PV_B3P_SemanticCallersSuccess227
import PV_B3P_CarrySuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev DigestQ := Array aspis_core.field.QM31 8#usize
abbrev DigestM := Array U32 8#usize
abbrev FrontierM := Array DigestM 20#usize

/-- A continuation rule for the emitted optional-recipient join point. -/
theorem recipient_cps {β : Type} (recipient : Option DigestM) (output : DigestQ)
    (opened : Array aspis_core.field.QM31 16#usize) (selectors : reference_copy_terminal.Selectors)
    (f : DigestQ → Result β) (hf : ∀ next, Success (f next)) :
    Success (match recipient with
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
theorem digest_level_cps {β : Type} (output : DigestQ) (opened : Array aspis_core.field.QM31 16#usize)
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

#print axioms recipient_cps
#print axioms digest_level_cps

theorem public_digest_success (p : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    Success (reference_terminal.public_digest_lanes p openings selectors) := by
  unfold reference_terminal.public_digest_lanes
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector0
  apply bind
  · apply total_reference_terminal_add_digest_binding <;> scalar_tac
  intro digests0
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector1
  apply bind
  · apply total_reference_terminal_add_digest_binding <;> scalar_tac
  intro digests1
  apply recipient_cps
  intro digests2
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selector3
  apply bind
  · apply total_reference_terminal_add_digest_binding <;> scalar_tac
  intro digests3
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level0
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level1
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level2
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level3
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level4
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level5
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level6
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level7
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level8
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level9
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level10
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level11
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level12
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level13
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level14
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level15
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level16
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level17
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level18
  apply lift_total
  apply lift_total
  apply lift_total
  apply digest_level_cps
  · scalar_tac
  · apply wrap_add_bound
    scalar_tac
  intro level19
  apply lift_total
  apply lift_total
  apply bind
  · apply row_total
    apply row_address_bound <;> scalar_tac
  intro selectorlast
  apply bind
  · apply total_reference_terminal_add_digest_binding <;> scalar_tac
  intro digestslast
  apply bind
  · exact carry_total p.transition.live_snapshot.next_pair_index
  intro carry
  split
  · apply lift_total
    apply lift_total
    apply lift_total
    apply bind
    · apply row_total
      apply row_address_bound
      · apply wrap_add_bound
        scalar_tac
      · scalar_tac
    intro selector
    apply bind
    · apply index <;> scalar_tac
    intro expected
    apply total_reference_terminal_add_digest_binding <;> scalar_tac
  · exact ok _

#print axioms public_digest_success
end PV_B3P_Success227
