import S6NativeLateDecoderFactoredV1
import S6NativeLateWordReadV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateDecodeTotal
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeLateDecoderFactored

@[step] theorem option_ne_graph (a b : Option U64) :
    core.cmp.PartialEq.ne.default
      (core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU64) a b
      ⦃ result => result=decide (a≠b) ⦄ := by
  unfold core.cmp.PartialEq.ne.default
  step*
  all_goals simp_all

@[step] theorem decode_spec (bytes : Slice U8) : decode bytes ⦃ _ => True ⦄ := by
  unfold decode POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
    core.option.Option.Insts.CoreCmpPartialEqOption
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*

theorem decode_total (bytes : Slice U8) :
    ∃ result, decode_pool_v1_pair_late_public_statement_boxed_v1 bytes=ok result := by
  obtain ⟨result,run,_⟩ := spec_imp_exists (decode_spec bytes)
  exact ⟨result,(decode_source bytes).symm.trans run⟩

#print axioms option_ne_graph
#print axioms decode_total
end AspisS6NativeLateDecodeTotal
