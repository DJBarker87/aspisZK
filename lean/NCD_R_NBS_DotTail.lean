-- Retargeted inherited proof body; only module imports changed.
import NCD_R_NBS_DotTerm
import NBQ_TailDomain
import NCD_R_JFs_TX2_TailStages
import RPu_JFs_TX2_TailQM
set_option autoImplicit false
noncomputable section
namespace NBS_DotTail
open Aeneas Aeneas.Std Result AspisR1
/-- Only the input QM31 decoder domain, on the SAME q and offsets. -/
def Domain (q : Array U8 608#usize) (slot : Fin 4) : Prop :=
  ∀ kind : Fin 3, ∃ value,
    JFr_TX2_TailRead.read q (JFr_TX2_Tails.offset slot kind) (JFr_TX2_Tails.stop slot kind)=ok value

theorem source (q : Array U8 608#usize) (slot : Fin 4) (decoded : Domain q slot)
    (g : Array FIo_Install.NE 29#usize) (hg : FIo_ArrayCanon.Holds g) :
    ∃ out, JFs_TX2_DotSuffix.tail q g
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨q0,r0⟩ := decoded 0
  obtain ⟨q1,r1⟩ := decoded 1
  obtain ⟨q2,r2⟩ := decoded 2
  have c0 := JFs_TX2_TailQM.source _ _ _ q0 r0
  have c1 := JFs_TX2_TailQM.source _ _ _ q1 r1
  have c2 := JFs_TX2_TailQM.source _ _ _ q2 r2
  obtain ⟨g28,hg28,m28⟩ := JFs_TX2_ArrayRead.source g 28#usize (by decide)
  obtain ⟨g26,hg26,m26⟩ := JFs_TX2_ArrayRead.source g 26#usize (by decide)
  obtain ⟨g27,hg27,m27⟩ := JFs_TX2_ArrayRead.source g 27#usize (by decide)
  obtain ⟨s0,s1,s2,s3,out,new,p0,p1,p2,_,_,_,_,_,finished,canonical⟩ :=
    NBQ_TailDomain.three g28 g26 g27 q0 q1 q2 (hg g28 m28) (hg g26 m26) (hg g27 m27) c0 c1 c2
  refine ⟨out,?_,canonical⟩
  rw [JFs_TX2_TailStages.body]
  simp only [JFs_TX2_TailStages.source,new,hg28,hg26,hg27,r0,r1,r2,p0,p1,p2,finished,
    bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.unwrap]

#print axioms source
end NBS_DotTail
