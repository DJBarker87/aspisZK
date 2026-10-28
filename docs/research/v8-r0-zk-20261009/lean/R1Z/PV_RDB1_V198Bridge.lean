import R1Z.PV_RDB1_Copy
import R1Z.PV_RDB1_V198
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V198Bridge
open PV_RDB1_Copy PV_RDB1_V198

def chunk (a : U32) : List U8 := (core.num.U32.to_le_bytes a).val

theorem chunk_length (a : U32) : (chunk a).length=4 :=
  (core.num.U32.to_le_bytes a).property

def pairCopies (a b : U32) (out : List U8) : List U8 :=
  copies out 0 [chunk a,chunk b]

theorem pair_result (a b : U32) (out : List U8) :
    pairCopies a b out = words a b ++ out.drop 8 := by
  change copies out 0 [chunk a,chunk b] = words a b ++ out.drop 8
  have h := copies_result [chunk a,chunk b] [] out
  have hf : [chunk a,chunk b].flatten = words a b := by
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil,chunk,words]
  simpa only [List.nil_append,List.length_nil,hf,words_length] using h

theorem two_pairs_result (a b c d : U32) (out : List U8) :
    copies (pairCopies a b out) 8 [chunk c,chunk d] =
      words a b ++ words c d ++ out.drop 16 := by
  rw [pair_result]
  have h := copies_result [chunk c,chunk d] (words a b) (out.drop 8)
  have hf : [chunk c,chunk d].flatten = words c d := by
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil,chunk,words]
  simpa only [hf,words_length,List.drop_drop] using h

def native (a b c d : U32) (out : List U8) : Execution :=
  if out.length < 8 then ⟨fail .panic,out⟩ else
  let first := pairCopies a b out
  if first.length < 16 then ⟨fail .panic,first⟩ else
  ⟨ok (),copies first 8 [chunk c,chunk d]⟩

/-- The four real copy operations and ordered outer checks have exactly the
complete return/buffer law, including partial writes on second-range panic. -/
theorem source_complete (a b c d : U32) (out : List U8) :
    native a b c d out = write a b c d out := by
  by_cases h8 : out.length < 8
  · simp only [native,write,h8,ite_true]
  · have hl : (pairCopies a b out).length=out.length := by
      rw [pair_result,List.length_append,words_length,List.length_drop]
      omega
    simp only [native,write,h8,ite_false,hl]
    split
    · rw [pair_result]
    · rw [two_pairs_result]

/-- Both 4-byte sources fit within each 8-byte parent slice. The source
copy-length mismatch panic is unreachable after that parent check. -/
theorem inner_bounds (a b : U32) :
    (chunk a).length=4 ∧ (chunk b).length=4 ∧
    0+4 ≤ 8 ∧ 4+4 ≤ 8 := ⟨chunk_length a,chunk_length b,by omega,by omega⟩

#print axioms chunk_length
#print axioms pair_result
#print axioms two_pairs_result
#print axioms source_complete
#print axioms inner_bounds
end R1Z.PV_RDB1_V198Bridge
