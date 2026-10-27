import RPv_FJk_CopyDescriptor
import RPv_CopyLinkBitArithmetic
set_option autoImplicit false
namespace AspisR1.FJk_CopyWeightBits
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
/-- Shift/mask/cast VALUE on the original weight-kind4 run. -/
theorem keep (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (out : U32)
    (hk : l.weight_kind=4#u8) (hl : l.weight_level.val<64)
    (run : link_weight l index v=ok out) :
    out.val=((index.val>>>l.weight_level.val)&&&1) ∧ out.val≤1 := by
  obtain ⟨shifted,bit,w,hs,hb,hc,hv,hw⟩ :=
    CopyLinkBitArithmetic.shifted_bit_success index l.weight_level hl
  unfold link_weight at run
  rw [hk] at run
  change (do
    let shifted ← index >>> l.weight_level
    let bit ← lift (shifted &&& 1#u64)
    let w ← lift (UScalar.cast .U32 bit)
    ok w)=ok out at run
  rw [hs,bind_tc_ok,hb,bind_tc_ok,hc,bind_tc_ok] at run
  cases Result.ok.inj run
  exact ⟨hv,hw⟩
/-- Natural subtraction, exactly as in the installed source and retained model. -/
theorem complement (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (out : U32)
    (hk : l.weight_kind=3#u8) (hl : l.weight_level.val<64)
    (run : link_weight l index v=ok out) :
    out.val=1-((index.val>>>l.weight_level.val)&&&1) ∧ out.val≤1 := by
  obtain ⟨shifted,bit,w,hs,hb,hc,hv,hw⟩ :=
    CopyLinkBitArithmetic.shifted_bit_success index l.weight_level hl
  obtain ⟨c,cs,cv,cb⟩ := CopyLinkBitArithmetic.one_minus_bit_success w hw
  unfold link_weight at run
  rw [hk] at run
  change (do
    let shifted ← index >>> l.weight_level
    let bit ← lift (shifted &&& 1#u64)
    let w ← lift (UScalar.cast .U32 bit)
    let c ← 1#u32 - w
    ok c)=ok out at run
  rw [hs,bind_tc_ok,hb,bind_tc_ok,hc,bind_tc_ok,cs,bind_tc_ok] at run
  cases Result.ok.inj run
  exact ⟨cv.trans (congrArg (1-·) hv),cb⟩
#print axioms keep
#print axioms complement
end AspisR1.FJk_CopyWeightBits
