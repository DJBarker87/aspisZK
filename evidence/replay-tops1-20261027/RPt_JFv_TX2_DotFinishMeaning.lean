import RPt_JFv_TX2_CanonicalMeaning
import RPt_JFs_TX2_DotFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_DotFinishMeaning
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap

def cell {α : Type} (a : Array α 4#usize) (j : Fin 4) : α :=
  a.val[j.val]'(by rw [a.property];exact j.isLt)

theorem source (s : FIo_Native.fast_pairing.canonical.Dot) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.finish s=ok out ∧
      JFs_TX2_DotFinish.Canon out ∧
      ∀ j : Fin 4, (cell out j).val=(cell s.sums j).val%2147483647 := by
  obtain ⟨out,run,canon⟩ := JFs_TX2_DotFinish.source s
  refine ⟨out,run,canon,?_⟩
  rcases s with ⟨a⟩
  obtain ⟨s0,s1,s2,s3,rfl⟩ := shape a
  have r0 : Array.index_usize (pack s0 s1 s2 s3) 0#usize=ok s0 := rfl
  have r1 : Array.index_usize (pack s0 s1 s2 s3) 1#usize=ok s1 := rfl
  have r2 : Array.index_usize (pack s0 s1 s2 s3) 2#usize=ok s2 := rfl
  have r3 : Array.index_usize (pack s0 s1 s2 s3) 3#usize=ok s3 := rfl
  unfold FIo_Native.fast_pairing.canonical.Dot.finish at run
  simp only [r0,r1,r2,r3,bind_tc_ok] at run
  obtain ⟨m0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m2,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨m3,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : pack m0 m1 m2 m3=out := Result.ok.inj run
  subst out
  intro j
  fin_cases j
  · exact JFv_TX2_CanonicalMeaning.source s0 m0 h0
  · exact JFv_TX2_CanonicalMeaning.source s1 m1 h1
  · exact JFv_TX2_CanonicalMeaning.source s2 m2 h2
  · exact JFv_TX2_CanonicalMeaning.source s3 m3 h3
#print axioms source
end AspisR1.JFv_TX2_DotFinishMeaning
end
