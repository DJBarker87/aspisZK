import RPt_JFv_TX2_FromLimbsMeaning
import RPt_JFv_TX2_ArrayMeaning
import RPt_JFs_TX2_ScalarFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_ScalarMeaning
open Aeneas Aeneas.Std Result JFs_TX2_Eight
open JFv_TX2_ArrayMeaning (cell)

theorem value (a : Array U64 8#usize) (out : FIo_Install.NE)
    (run : JFs_TX2_DotSuffix.scalarFinish a=ok out) :
    ∀ j : Fin 8, (cell (JFv_TX2_FromLimbsMeaning.limbs out) j).val=(cell a j).val%2147483647 := by
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7,rfl⟩ := JFs_TX2_ArrayEight.shape a
  have r0 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 0#usize=ok s0 := rfl
  have r1 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 1#usize=ok s1 := rfl
  have r2 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 2#usize=ok s2 := rfl
  have r3 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 3#usize=ok s3 := rfl
  have r4 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 4#usize=ok s4 := rfl
  have r5 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 5#usize=ok s5 := rfl
  have r6 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 6#usize=ok s6 := rfl
  have r7 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 7#usize=ok s7 := rfl
  unfold JFs_TX2_DotSuffix.scalarFinish at run
  simp only [r0,r1,r2,r3,r4,r5,r6,r7,bind_tc_ok] at run
  obtain ⟨m0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m2,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m3,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m4,h4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m5,h5,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m6,h6,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m7,h7,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some v =>
    simp only [core.option.Option.unwrap,bind_tc_ok] at run
    have same : v=out := Result.ok.inj run
    subst out
    have words := JFv_TX2_FromLimbsMeaning.source _ v ho
    rw [words]
    intro j
    fin_cases j
    · exact (FIo_ReduceValues.m31_value s0 m0 h0).1
    · exact (FIo_ReduceValues.m31_value s1 m1 h1).1
    · exact (FIo_ReduceValues.m31_value s2 m2 h2).1
    · exact (FIo_ReduceValues.m31_value s3 m3 h3).1
    · exact (FIo_ReduceValues.m31_value s4 m4 h4).1
    · exact (FIo_ReduceValues.m31_value s5 m5 h5).1
    · exact (FIo_ReduceValues.m31_value s6 m6 h6).1
    · exact (FIo_ReduceValues.m31_value s7 m7 h7).1

theorem source (a : Array U64 8#usize) :
    ∃ out, JFs_TX2_DotSuffix.scalarFinish a=ok out ∧ FIo_WideValues.Canon out ∧
      ∀ j : Fin 8, (cell (JFv_TX2_FromLimbsMeaning.limbs out) j).val=(cell a j).val%2147483647 := by
  obtain ⟨out,run,canon⟩ := JFs_TX2_ScalarFinish.source a
  exact ⟨out,run,canon,value a out run⟩
#print axioms value
#print axioms source
end AspisR1.JFv_TX2_ScalarMeaning
end
