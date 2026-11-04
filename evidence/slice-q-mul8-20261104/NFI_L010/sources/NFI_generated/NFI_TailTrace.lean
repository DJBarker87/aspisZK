import NFI_TraceResult
import NFI_InnerCut
import NFF_LoggedTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_TailTrace
open Aeneas Aeneas.Std Result NFI_TraceResult
abbrev Input := NFI_InnerCut.Input
structure Cut (input : Input) where
  ordinal : Nat
  receiver : FIo_Native.fast_pairing.EbyKDot

def run (oracle : NFF_ProductCall.Oracle) (input : Input) : M (Cut input) NEV_DotCarrier.NE := do
  let q := input.q
  let g := input.g
  let slot := input.slot
  let tail ← lift (FIo_Native.fast_pairing.EbyKDot.new)
  mark (⟨0,tail⟩ : Cut input)
  let we ← lift (Array.index_usize g 28#usize)
  let i8 ← lift (slot * 120#usize)
  let i9 ← lift (i8 + 104#usize)
  let i10 ← lift (i8 + 120#usize)
  let s ← lift (core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := i9, «end» := i10 })
  let o1 ← lift (AspisR1.FIp_DotDecode.field.QM31.from_le_bytes s)
  let q1 ← lift (core.option.Option.unwrap o1)
  let (r, tail1) ← lift (NFF_LoggedPush.publicPush oracle tail we q1)
  mark (⟨1,tail1⟩ : Cut input)
  let _ ← lift (core.result.Result.unwrap core.fmt.DebugUnit r)
  let i11 ← lift (slot * 32#usize)
  let i12 ← lift (480#usize + i11)
  let i13 ← lift (0#usize * 16#usize)
  let offset0 ← lift (i12 + i13)
  let i14 ← lift (0#usize + 26#usize)
  let we1 ← lift (Array.index_usize g i14)
  let i15 ← lift (offset0 + 16#usize)
  let s1 ← lift (core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := offset0, «end» := i15 })
  let o2 ← lift (AspisR1.FIp_DotDecode.field.QM31.from_le_bytes s1)
  let q2 ← lift (core.option.Option.unwrap o2)
  let (r1, tail2) ← lift (NFF_LoggedPush.publicPush oracle tail1 we1 q2)
  mark (⟨2,tail2⟩ : Cut input)
  let _ ← lift (core.result.Result.unwrap core.fmt.DebugUnit r1)
  let i16 ← lift (480#usize + i11)
  let i17 ← lift (1#usize * 16#usize)
  let offset1 ← lift (i16 + i17)
  let i18 ← lift (1#usize + 26#usize)
  let we2 ← lift (Array.index_usize g i18)
  let i19 ← lift (offset1 + 16#usize)
  let s2 ← lift (core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := offset1, «end» := i19 })
  let o3 ← lift (AspisR1.FIp_DotDecode.field.QM31.from_le_bytes s2)
  let q3 ← lift (core.option.Option.unwrap o3)
  let (r2, tail3) ← lift (NFF_LoggedPush.publicPush oracle tail2 we2 q3)
  mark (⟨3,tail3⟩ : Cut input)
  let _ ← lift (core.result.Result.unwrap core.fmt.DebugUnit r2)
  let we3 ← lift (FIo_Native.fast_pairing.EbyKDot.finish tail3)
  pure we3

theorem erased (oracle : NFF_ProductCall.Oracle) (input : Input) :
    (run oracle input).result=NFF_LoggedTail.run oracle input.q input.g input.slot := by
  have right {T : Type} (r : Result T) : (do let x ← r; ok x)=r := by cases r <;> rfl
  simp only [run,NFF_LoggedTail.run,erase_bind,erase_lift,erase_mark,erase_pure,Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok,right]

theorem emitted (oracle : NFF_ProductCall.Oracle) (law : NFF_ProductCall.Law oracle)
    (input : Input) :
    (run oracle input).result=NFE_NFA_SuffixFactor.tail input.q input.g input.slot := by
  rw [erased,NFF_LoggedTail.replay oracle law]

#print axioms erased
#print axioms emitted
end AspisR1.NFI_TailTrace
end
