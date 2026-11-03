import NEI_DotFinishRaw.Funs
import NEI_ReductionWord
set_option autoImplicit false
noncomputable section
namespace NEI_DotReduction
open Aeneas Aeneas.Std Result AspisR1
/-- The actual checked word operations equal the coherent wrapping model on
EVERY U64, including the overflow/domain obligations of both folds. -/
theorem same (x : U64) : NEI_DotFinishRaw.fast_pairing.canonical.reduce x =
 FIo_Native.fast_pairing.canonical.reduce x := by
 have castP : core.convert.num.FromU64U32.from 2147483647#u32 = 2147483647#u64 := rfl
 unfold NEI_DotFinishRaw.fast_pairing.canonical.reduce FIo_Native.fast_pairing.canonical.reduce
 simp only [NEI_DotFinishRaw.fast_pairing.canonical.P,FIo_Native.fast_pairing.canonical.P,lift,bind_tc_ok,castP]
 rw [FIo_ReduceFacts.shr31]
 simp only [bind_tc_ok]
 rw [FIo_ReduceBounds.checked]
 simp only [bind_tc_ok]
 rw [FIo_ReduceFacts.shr31]
 simp only [bind_tc_ok]
 rw [FIo_ReduceBounds.checked]
 simp only [bind_tc_ok]
 let folded := FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)
 change (if folded ≥ 2147483647#u64 then
   (do let z ← folded-2147483647#u64;ok (UScalar.cast .U32 z))
   else ok (UScalar.cast .U32 folded)) =
   (if folded ≥ 2147483647#u64 then
    ok (UScalar.cast .U32 (U64.wrapping_sub folded 2147483647#u64))
    else ok (UScalar.cast .U32 folded))
 split
 · rename_i h
   rw [FIo_ScalarBridge.sub _ _ (by scalar_tac)]
   simp only [bind_tc_ok,if_pos h]
 · rename_i h
   simp only [if_neg h]
/-- Reuse the established modulo/canonical-value theorem, no reduction replay. -/
theorem value (x : U64) : ∃ z,
 NEI_DotFinishRaw.fast_pairing.canonical.reduce x = ok z ∧
 z.val=x.val%2147483647 ∧ z.val<2147483647 := by
 rw [same]
 exact NEI_ReductionWord.native_reduce x
#print axioms same
#print axioms value
end NEI_DotReduction
end
