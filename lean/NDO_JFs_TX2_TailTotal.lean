import NDO_JFs_TX2_TailStages
import RPu_JFs_TX2_TailQM
import NDO_JFs_TX2_EbyKPush
import NDO_JFs_TX2_EbyKFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_TailTotal
open Aeneas Aeneas.Std Result

def initial : FIo_Native.fast_pairing.EbyKDot :=
  ⟨⟨Array.repeat 4#usize 0#u64⟩,⟨Array.repeat 4#usize 0#u64⟩,0#usize⟩

theorem source (i : Fin 12) (slot : Fin 4) (g : Array FIo_Install.NE 29#usize) :
    ∃ out, JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array (JFn_Values.position i)) g
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac))=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨q0,hq0⟩ := JFr_TX2_Tails.source i slot 0
  obtain ⟨q1,hq1⟩ := JFr_TX2_Tails.source i slot 1
  obtain ⟨q2,hq2⟩ := JFr_TX2_Tails.source i slot 2
  have position : JFr_TX2_Tails.position i=JFn_Values.position i := by
    apply Fin.ext
    change i.val+10=10+i.val
    omega
  rw [position] at hq0 hq1 hq2
  have c0 := JFs_TX2_TailQM.source _ _ _ q0 hq0
  have c1 := JFs_TX2_TailQM.source _ _ _ q1 hq1
  have c2 := JFs_TX2_TailQM.source _ _ _ q2 hq2
  obtain ⟨g28,hg28,_⟩ := JFs_TX2_ArrayRead.source g 28#usize (by decide)
  obtain ⟨g26,hg26,_⟩ := JFs_TX2_ArrayRead.source g 26#usize (by decide)
  obtain ⟨g27,hg27,_⟩ := JFs_TX2_ArrayRead.source g 27#usize (by decide)
  obtain ⟨s0,h0,n0⟩ := JFs_TX2_EbyKPush.source initial g28 q0 c0 (by change 0<256;decide)
  obtain ⟨s1,h1,n1⟩ := JFs_TX2_EbyKPush.source s0 g26 q1 c1 (by rw [n0];change 0+1<256;decide)
  obtain ⟨s2,h2,_⟩ := JFs_TX2_EbyKPush.source s1 g27 q2 c2 (by rw [n1,n0];change 0+1+1<256;decide)
  obtain ⟨out,ho,canon⟩ := JFs_TX2_EbyKFinish.source s2
  have hn : FIo_Native.fast_pairing.EbyKDot.new=ok initial := rfl
  refine ⟨out,?_,canon⟩
  rw [JFs_TX2_TailStages.body]
  simp only [JFs_TX2_TailStages.source,hn,hg28,hg26,hg27,hq0,hq1,hq2,h0,h1,h2,ho,
    bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.unwrap]

#print axioms source
end AspisR1.JFs_TX2_TailTotal
end
