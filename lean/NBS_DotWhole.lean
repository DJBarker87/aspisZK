import NBS_DotOuter
import NBS_DotTail
import JFs_TX2_ScalarFinish
import JFs_TX2_WideAdd
set_option autoImplicit false
noncomputable section
namespace NBS_DotWhole
open Aeneas Aeneas.Std Result AspisR1
/-- Complete selected-model helper on arbitrary source-valid input buffers
and arbitrary canonical powers. Prefix loops, reductions, all three tail calls
and final addition share the SAME carriers. Native association and the reached
caller producer domain remain separate obligations. -/
theorem source (q : Array U8 608#usize) (slot : Fin 4)
    (g : Array FIo_Install.NE 29#usize) (hg : FIo_ArrayCanon.Holds g)
    (decoded : NBS_DotTerm.Scalars q (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)))
    (tails : NBS_DotTail.Domain q slot) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots_one q g
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨limbs,loopRun,_⟩ := NBS_DotOuter.source q _ decoded g hg
  obtain ⟨head,headRun,headCanon⟩ := JFs_TX2_ScalarFinish.source limbs
  obtain ⟨tail,tailRun,tailCanon⟩ := NBS_DotTail.source q slot tails g hg
  obtain ⟨out,addRun,canonical⟩ := JFs_TX2_WideAdd.source head tail headCanon tailCanon
  refine ⟨out,?_,canonical⟩
  rw [JFs_TX2_DotSuffix.body]
  simp only [JFs_TX2_Iterator.initial,loopRun,headRun,tailRun,addRun,bind_tc_ok]

#print axioms source
end NBS_DotWhole
