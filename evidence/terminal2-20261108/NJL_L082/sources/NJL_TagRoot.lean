import NJL_TagMeaning
import NJL_TagSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open NJL_TagRawTrace (Selectors)
def zero : NJL_TagReduction.State := fun _=>0#u32
def reference (s : Selectors) (c : Fin 30) : Result NQ := do
 let words ← NJL_TagChunks.run s (NJL_TagPartition.chunks 68 (NJL_TagData.indices c)) zero
 ok (NJB_Words.value words)
/-- Full positive216 invocation on arbitrary SAME canonical high selectors:
exact registry interval, native source chunk schedule, actual raw/reduction
traces, all four returned words and exact-field tagged-coordinate meaning. -/
theorem source (s : Selectors) (c : Fin 30) (hs : FIw_ArrayValue.canonical s.high) :
 ∃ after,reference s c=ok (NJB_Words.value after) ∧
 NJL_TagSchedule.Schedule (NJL_TagData.indices c) (NJL_TagPartition.chunks 68 (NJL_TagData.indices c)) ∧
 NJL_TagChunks.Trace s (NJL_TagPartition.chunks 68 (NJL_TagData.indices c)) zero after ∧
 Canon (NJB_Words.value after) ∧
 decode (NJB_Words.value after)=NJL_TagMeaning.model s (NJL_TagData.indices c) := by
 obtain ⟨after,call,trace,ha,va⟩ := NJL_TagChunks.source s _ zero (NJL_TagPartition.coordinate c).2 hs (by intro i;change 0<2147483647;decide)
 refine ⟨after,?_,(NJL_TagSchedule.coordinate c).1,trace,?_,?_⟩
 · simp only [reference,call,bind_tc_ok]
 · exact ⟨⟨ha 0,ha 1⟩,⟨ha 2,ha 3⟩⟩
 · rw [←NJL_TagMeaning.encode_decode,NJB_Words.word_value]
   have words : (fun i=>((after i).val : ExtractedMaskQM31Exact.M31Exact))=
     (fun i=>(NJL_TagRawTrace.dot s (NJL_TagData.indices c) i : ExtractedMaskQM31Exact.M31Exact)) := by
    funext i
    have val := va i
    rw [(NJL_TagPartition.coordinate c).1] at val
    have initial : (zero i).val=0 := rfl
    rw [initial,Nat.zero_add] at val
    rw [val]
    exact NJL_TagMeaning.residue _
   rw [words]
   exact NJL_TagMeaning.value _ _
#print source
#print axioms source
end AspisR1.NJL_TagRoot
end
