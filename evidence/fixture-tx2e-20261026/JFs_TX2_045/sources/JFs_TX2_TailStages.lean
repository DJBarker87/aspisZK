import JFs_TX2_DotSuffix
import JFr_TX2_Tails
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_TailStages
open Aeneas Aeneas.Std Result

def source (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize) (slot : Fin 4) : Result FIo_Install.NE := do
  let initial ← FIo_Native.fast_pairing.EbyKDot.new
  let g28 ← Array.index_usize g 28#usize
  let q28 ← JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot 0) (JFr_TX2_Tails.stop slot 0)
  let (r0,s0) ← FIo_Native.fast_pairing.EbyKDot.push initial g28 q28
  core.result.Result.unwrap core.fmt.DebugUnit r0
  let g26 ← Array.index_usize g 26#usize
  let q26 ← JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot 1) (JFr_TX2_Tails.stop slot 1)
  let (r1,s1) ← FIo_Native.fast_pairing.EbyKDot.push s0 g26 q26
  core.result.Result.unwrap core.fmt.DebugUnit r1
  let g27 ← Array.index_usize g 27#usize
  let q27 ← JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot 2) (JFr_TX2_Tails.stop slot 2)
  let (r2,s2) ← FIo_Native.fast_pairing.EbyKDot.push s1 g27 q27
  core.result.Result.unwrap core.fmt.DebugUnit r2
  let out ← FIo_Native.fast_pairing.EbyKDot.finish s2
  ok out

theorem body (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize) (slot : Fin 4) :
    JFs_TX2_DotSuffix.tail q g (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=source q g slot := by
  fin_cases slot <;>
    simp only [JFs_TX2_DotSuffix.tail,source,JFr_TX2_TailRead.read,
      JFr_TX2_Tails.offset,JFr_TX2_Tails.stop,JFr_TX2_Tails.start,
      bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry] <;> rfl

#print axioms body
end AspisR1.JFs_TX2_TailStages
end
