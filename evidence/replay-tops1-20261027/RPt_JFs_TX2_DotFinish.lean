import RPt_JFs_TX2_CanonicalReduce
import RPt_JFs_TX2_FromLimbs
import RPt_JFs_TX2_RawMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_DotFinish
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
def Canon (a : FIo_Native.fast_pairing.canonical.Q) : Prop := ∀ x∈a.val,x.val<2147483647
theorem packed (s0 s1 s2 s3 : U64) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.finish ⟨pack s0 s1 s2 s3⟩=ok out ∧ Canon out := by
  have r0 : Array.index_usize (pack s0 s1 s2 s3) 0#usize=ok s0 := rfl
  obtain ⟨m0,h0,c0⟩ := JFs_TX2_CanonicalReduce.source s0
  have r1 : Array.index_usize (pack s0 s1 s2 s3) 1#usize=ok s1 := rfl
  obtain ⟨m1,h1,c1⟩ := JFs_TX2_CanonicalReduce.source s1
  have r2 : Array.index_usize (pack s0 s1 s2 s3) 2#usize=ok s2 := rfl
  obtain ⟨m2,h2,c2⟩ := JFs_TX2_CanonicalReduce.source s2
  have r3 : Array.index_usize (pack s0 s1 s2 s3) 3#usize=ok s3 := rfl
  obtain ⟨m3,h3,c3⟩ := JFs_TX2_CanonicalReduce.source s3
  refine ⟨pack m0 m1 m2 m3,?_,?_⟩
  · simp only [FIo_Native.fast_pairing.canonical.Dot.finish,r0,r1,r2,r3,h0,h1,h2,h3,bind_tc_ok]
    rfl
  · intro x hx
    change x∈[m0,m1,m2,m3] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact c0
    · exact c1
    · exact c2
    · exact c3

theorem source (s : Dot) : ∃ out, FIo_Native.fast_pairing.canonical.Dot.finish s=ok out ∧ Canon out := by
  rcases s with ⟨s⟩
  obtain ⟨s0,s1,s2,s3,rfl⟩ := shape s
  exact packed s0 s1 s2 s3

#print axioms packed
#print axioms source
end AspisR1.JFs_TX2_DotFinish
end
