import RPu_JFs_TX2_DotSuffix
import NDO_JFr_TX2_Tails
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
  fin_cases slot
  · simp only [JFs_TX2_DotSuffix.tail,source,JFr_TX2_TailRead.read,
      JFr_TX2_Tails.offset,JFr_TX2_Tails.stop,JFr_TX2_Tails.start,
      bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry,
      show 0#usize*120#usize=ok 0#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 0#usize+104#usize=ok 104#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize+120#usize=ok 120#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize*32#usize=ok 0#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 480#usize+0#usize=ok 480#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize*16#usize=ok 0#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 480#usize+0#usize=ok 480#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize+26#usize=ok 26#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 480#usize+16#usize=ok 496#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 1#usize*16#usize=ok 16#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 1#usize+26#usize=ok 27#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 496#usize+16#usize=ok 512#usize from Port4A_ReaderInstall.add_value _ _ (by decide)]
    rfl
  · simp only [JFs_TX2_DotSuffix.tail,source,JFr_TX2_TailRead.read,
      JFr_TX2_Tails.offset,JFr_TX2_Tails.stop,JFr_TX2_Tails.start,
      bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry,
      show 1#usize*120#usize=ok 120#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 120#usize+104#usize=ok 224#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 120#usize+120#usize=ok 240#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 1#usize*32#usize=ok 32#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 480#usize+32#usize=ok 512#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize*16#usize=ok 0#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 512#usize+0#usize=ok 512#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize+26#usize=ok 26#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 512#usize+16#usize=ok 528#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 1#usize*16#usize=ok 16#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 1#usize+26#usize=ok 27#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 528#usize+16#usize=ok 544#usize from Port4A_ReaderInstall.add_value _ _ (by decide)]
    rfl
  · simp only [JFs_TX2_DotSuffix.tail,source,JFr_TX2_TailRead.read,
      JFr_TX2_Tails.offset,JFr_TX2_Tails.stop,JFr_TX2_Tails.start,
      bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry,
      show 2#usize*120#usize=ok 240#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 240#usize+104#usize=ok 344#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 240#usize+120#usize=ok 360#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 2#usize*32#usize=ok 64#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 480#usize+64#usize=ok 544#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize*16#usize=ok 0#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 544#usize+0#usize=ok 544#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize+26#usize=ok 26#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 544#usize+16#usize=ok 560#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 1#usize*16#usize=ok 16#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 1#usize+26#usize=ok 27#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 560#usize+16#usize=ok 576#usize from Port4A_ReaderInstall.add_value _ _ (by decide)]
    rfl
  · simp only [JFs_TX2_DotSuffix.tail,source,JFr_TX2_TailRead.read,
      JFr_TX2_Tails.offset,JFr_TX2_Tails.stop,JFr_TX2_Tails.start,
      bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry,
      show 3#usize*120#usize=ok 360#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 360#usize+104#usize=ok 464#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 360#usize+120#usize=ok 480#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 3#usize*32#usize=ok 96#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 480#usize+96#usize=ok 576#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize*16#usize=ok 0#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 576#usize+0#usize=ok 576#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 0#usize+26#usize=ok 26#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 576#usize+16#usize=ok 592#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 1#usize*16#usize=ok 16#usize from Port4A_ReaderInstall.mul_value _ _ (by decide),
      show 1#usize+26#usize=ok 27#usize from Port4A_ReaderInstall.add_value _ _ (by decide),
      show 592#usize+16#usize=ok 608#usize from Port4A_ReaderInstall.add_value _ _ (by decide)]
    rfl
#print axioms body
end AspisR1.JFs_TX2_TailStages
end
