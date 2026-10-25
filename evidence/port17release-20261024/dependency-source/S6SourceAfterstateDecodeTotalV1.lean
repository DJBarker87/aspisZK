import S6AfterstateDecoderPart0TotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Total
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

/-- TOTAL complete 688-byte afterstate decoder for arbitrary input slices.
All length, header, canonical digest and validator rejection paths are retained. -/
@[step] theorem decode_spec (bytes : Slice U8) :
    decode bytes ⦃ _ => True ⦄ := by
  unfold decode core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals step*

theorem source_total (bytes : Slice U8) :
    ∃ result, decode_pool_v1_pair_verified_afterstate_v1 bytes=ok result := by
  obtain ⟨result,h,_⟩ := spec_imp_exists (decode_spec bytes)
  exact ⟨result, (decode_source bytes).symm.trans h⟩

#print axioms decode_spec
#print axioms source_total
end AspisS6SourceCodec.AfterstateFactored.Total
