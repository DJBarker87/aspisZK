import NDN_PackedFrame
import NIH_RawSource
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_PackedBounds
open FIv_NativeArithmetic (NQ)
open FJb_TailCell (cell)
/-- The SAME raw output is constructed from this canonical input, and every
word satisfies the actual constructor's <2^62 domain. No output premise. -/
theorem raw (input : Array NQ 4#usize) (canonical : FIw_ArrayValue.canonical input) :
 ∃ out,FIq_Native.state_only_poseidon.external_local_packed_raw input=ok out ∧
 ∀ j : Fin 4,(cell out j).val<4611686018427387904 := by
 obtain ⟨out,run,value⟩:=NDN_PackedFrame.result input canonical
 refine ⟨out,run,?_⟩
 intro j
 rw [value j]
 have bounded:=FJe_RawReference.output_bound
   (FJe_PackedRawRowValue.words (FJe_PackedInputWords.mapped input))
   (FJe_PackedInputWords.bounded input canonical) j
 have small : 8*(7*AspisV8R15.ExactTowerBase.P)<4611686018427387904 := by
   change 8*(7*2147483647)<4611686018427387904
   omega
 exact lt_trans bounded small
#print axioms raw
end AspisR1.NIH_PackedBounds
end
