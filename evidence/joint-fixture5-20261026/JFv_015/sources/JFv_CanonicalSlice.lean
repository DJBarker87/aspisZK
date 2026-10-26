import JFv_WordCanonical
import MultiproofConeCanonicalAppend
set_option autoImplicit false
namespace AspisR1.JFv_CanonicalSlice
open Aeneas Aeneas.Std Result
open OraclePortCompactDraft MultiproofConeCanonical MultiproofConeCanonicalAppend

theorem selected (b : AspisV8R19.DuplexFrames.Bytes) (off n : Nat)
    (a : off%4=0) (z : n%4=0) (fits : off+n ≤ b.length)
    (canon : canonical b) : canonical (slice b off n) := by
  have tail := ((canonical_take_drop b off a (by omega)).mp canon).2
  have first := ((canonical_take_drop (b.drop off) n z (by rw [List.length_drop];omega)).mp tail).1
  exact first

theorem word (arr : Array U8 16#usize) (high low : Bool) :
    (JFv_QM31.word arr high low).val =
      (arr.val.drop ((if high then 8 else 0)+(if low then 4 else 0))).take 4 := by
  cases high <;> cases low <;>
    simp [JFv_QM31.word,CandidateCM31Parser.half0,CandidateCM31Parser.half1,
      CandidateQM31Parser.half0,CandidateQM31Parser.half1,ParserArraySlice.segment,
      List.drop_take,List.drop_drop,List.take_take]

theorem bounds (arr : Array U8 16#usize) (canon : canonical (bytesOf arr.val)) :
    ∀ high low,(core.num.U32.from_le_bytes (JFv_QM31.word arr high low)).val < 2147483647 := by
  intro high low
  apply JFv_WordCanonical.bound
  rw [word]
  simp only [bytesOf,List.map_take,List.map_drop]
  apply selected (bytesOf arr.val) _ 4
  · cases high <;> cases low <;> decide
  · decide
  · simp only [bytesOf,List.length_map,arr.property]
    cases high <;> cases low <;> decide
  · exact canon

#print axioms selected
#print axioms word
#print axioms bounds
end AspisR1.JFv_CanonicalSlice
