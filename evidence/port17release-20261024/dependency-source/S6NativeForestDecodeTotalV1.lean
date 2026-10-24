import S6NativeForestCommonDecodeV1
import S6NativeForestPaymentBoxesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeForestDecode
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

@[step] theorem decode_spec (bytes : Slice U8) :
    decode_pool_v1_pair_forest_terminal_statement_v1 bytes ⦃ _ => True ⦄ := by
  unfold decode_pool_v1_pair_forest_terminal_statement_v1
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*

theorem decode_total (bytes : Slice U8) :
    ∃ result,decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok result := by
  obtain ⟨result,run,_⟩ := spec_imp_exists (decode_spec bytes)
  exact ⟨result,run⟩

#print axioms decode_total
end AspisS6NativeForestDecode
