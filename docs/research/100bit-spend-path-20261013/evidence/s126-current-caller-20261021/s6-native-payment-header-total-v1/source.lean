import S6NativePaymentCommonDecodeV1
import S6StdByteSliceEqualityV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativePaymentDecode
open AspisR1TerminalDecoder
open pool_v1.payment_relation

def header_frame (bytes : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind) : Prop :=
  List.slice 0 4 bytes.val=magic.val ∧
  bytes.val[4]'(by rw [bytes.property]; decide)=1#u8 ∧
  bytes.val[5]'(by rw [bytes.property]; decide)=(read_discriminant kind : U8) ∧
  bytes.val[6]'(by rw [bytes.property]; decide)=1#u8 ∧
  bytes.val[7]'(by rw [bytes.property]; decide)=0#u8

@[step] theorem header_spec (bytes : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind) :
    require_header bytes magic kind ⦃ result => ∀ value,
      result=core.result.Result.Ok value → header_frame bytes magic kind ⦄ := by
  unfold require_header POOL_V1_PAYMENT_STATEMENT_VERSION
    pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*
  all_goals try exact AspisS6StdByteSlice.eq_spec _ _
  all_goals (intro value hv; cases hv)
  all_goals (simp_all [header_frame,List.slice,magic.property] <;> (repeat' constructor))
  all_goals first
    | scalar_tac
    | (have hm : List.take 4 magic.val=magic.val := by
         have h : List.take magic.val.length magic.val=magic.val := List.take_length
         simpa [magic.property] using h
       exact s_post1.symm.trans hm)

#print axioms header_spec
end AspisS6NativePaymentDecode
