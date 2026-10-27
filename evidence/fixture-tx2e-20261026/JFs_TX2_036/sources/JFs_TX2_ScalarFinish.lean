import JFs_TX2_DotSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_ScalarFinish
open Aeneas Aeneas.Std Result
open JFs_TX2_Eight
theorem source (limbs : Array U64 8#usize) :
    ∃ out, JFs_TX2_DotSuffix.scalarFinish limbs=ok out ∧ FIo_WideValues.Canon out := by
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7,rfl⟩ := JFs_TX2_ArrayEight.shape limbs
  have r0 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 0#usize=ok s0 := rfl
  obtain ⟨m0,h0,c0⟩ := JFs_TX2_Reduce.source s0
  have r1 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 1#usize=ok s1 := rfl
  obtain ⟨m1,h1,c1⟩ := JFs_TX2_Reduce.source s1
  have r2 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 2#usize=ok s2 := rfl
  obtain ⟨m2,h2,c2⟩ := JFs_TX2_Reduce.source s2
  have r3 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 3#usize=ok s3 := rfl
  obtain ⟨m3,h3,c3⟩ := JFs_TX2_Reduce.source s3
  have r4 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 4#usize=ok s4 := rfl
  obtain ⟨m4,h4,c4⟩ := JFs_TX2_Reduce.source s4
  have r5 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 5#usize=ok s5 := rfl
  obtain ⟨m5,h5,c5⟩ := JFs_TX2_Reduce.source s5
  have r6 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 6#usize=ok s6 := rfl
  obtain ⟨m6,h6,c6⟩ := JFs_TX2_Reduce.source s6
  have r7 : Array.index_usize (pack s0 s1 s2 s3 s4 s5 s6 s7) 7#usize=ok s7 := rfl
  obtain ⟨m7,h7,c7⟩ := JFs_TX2_Reduce.source s7
  obtain ⟨out,run,canon⟩ := JFs_TX2_FromLimbs.packed m0 m1 m2 m3 m4 m5 m6 m7
    ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩
  refine ⟨out,?_,canon⟩
  simp only [JFs_TX2_DotSuffix.scalarFinish,r0,r1,r2,r3,r4,r5,r6,r7,h0,h1,h2,h3,h4,h5,h6,h7,bind_tc_ok]
  change (do let o ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs (pack m0 m1 m2 m3 m4 m5 m6 m7)
             let v ← core.option.Option.unwrap o
             ok v)=ok out
  rw [run]
  rfl

#print axioms source
end AspisR1.JFs_TX2_ScalarFinish
end
