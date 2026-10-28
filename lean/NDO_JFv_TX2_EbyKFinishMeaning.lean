import RPu_JFv_TX2_DotFinishMeaning
import RPu_JFv_TX2_FromLimbsMeaning
import NDO_JFs_TX2_EbyKFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_EbyKFinishMeaning
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
open JFv_TX2_DotFinishMeaning (cell)

theorem source (s : FIo_Native.fast_pairing.EbyKDot) :
    ∃ (out : FIo_Install.NE) (a b : Array U32 4#usize), FIo_Native.fast_pairing.EbyKDot.finish s=ok out ∧ FIo_WideValues.Canon out ∧
      (JFv_TX2_FromLimbsMeaning.limbs out).val=a.val++b.val ∧
      (∀ j : Fin 4, (cell a j).val=(cell s.c0.sums j).val%2147483647) ∧
      (∀ j : Fin 4, (cell b j).val=(cell s.c1.sums j).val%2147483647) := by
  obtain ⟨out,run,canon⟩ := JFs_TX2_EbyKFinish.source s
  obtain ⟨a,ha,_,va⟩ := JFv_TX2_DotFinishMeaning.source s.c0
  obtain ⟨b,hb,_,vb⟩ := JFv_TX2_DotFinishMeaning.source s.c1
  refine ⟨out,a,b,run,canon,?_,va,vb⟩
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at ha
  rw [eb] at hb
  have r0 : Array.index_usize (pack a0 a1 a2 a3) 0#usize=ok a0 := rfl
  have r1 : Array.index_usize (pack a0 a1 a2 a3) 1#usize=ok a1 := rfl
  have r2 : Array.index_usize (pack a0 a1 a2 a3) 2#usize=ok a2 := rfl
  have r3 : Array.index_usize (pack a0 a1 a2 a3) 3#usize=ok a3 := rfl
  have r4 : Array.index_usize (pack a4 a5 a6 a7) 0#usize=ok a4 := rfl
  have r5 : Array.index_usize (pack a4 a5 a6 a7) 1#usize=ok a5 := rfl
  have r6 : Array.index_usize (pack a4 a5 a6 a7) 2#usize=ok a6 := rfl
  have r7 : Array.index_usize (pack a4 a5 a6 a7) 3#usize=ok a7 := rfl
  unfold FIo_Native.fast_pairing.EbyKDot.finish at run
  simp only [ha,hb,bind_tc_ok,FIo_Native.fast_pairing.canonical.Q.limbs,r0,r1,r2,r3,r4,r5,r6,r7] at run
  obtain ⟨o,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some v =>
    have same : v=out := Result.ok.inj run
    subst out
    rw [JFv_TX2_FromLimbsMeaning.source _ v ho,ea,eb]
    rfl
#print axioms source
end AspisR1.JFv_TX2_EbyKFinishMeaning
end
