import MultiproofConeExpansion

set_option autoImplicit false
namespace AspisR1.MultiproofConeExpansionLength
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft MultiproofConeCanonical MultiproofConeExpandModel

theorem expand_length (n : Nat) (wire : Bytes) (bound : 16*n ≤ wire.length) :
    (expand n wire).length = 32*n := by
  induction n generalizing wire with
  | zero => simp only [expand,List.range_zero,List.map_nil,List.flatten_nil,Nat.mul_zero,List.length_nil]
  | succ n ih =>
    have head : 16 ≤ wire.length := by omega
    rw [expand_step,List.length_append,List.length_append,List.length_take,
      Nat.min_eq_left head,List.length_replicate,ih (wire.drop 16) (by
        simp only [List.length_drop]
        omega)]
    omega

/-- Every reached compact semantic payload has exactly its modelled logical
length. The full checked loop and allocation bound are retained. -/
theorem empty_accumulator (bytes : Slice U8) (aligned : bytes.val.length%16=0)
    (capacity : 2*bytes.val.length≤Usize.max) :
    ∃ result, MultiproofParserRef.reference.expand_rows bytes (alloc.vec.Vec.new U8) = ok (some result) ∧
      bytesOf result.val = expand (bytes.val.length/16) (bytesOf bytes.val) ∧
      result.val.length = 2*bytes.val.length := by
  obtain ⟨result,hr,hm⟩ := MultiproofConeExpansion.expand_total bytes (alloc.vec.Vec.new U8) aligned
    (by simpa only [MultiproofConeVecLaws.empty_bytes,List.length_nil,Nat.zero_add] using capacity)
  simp only [MultiproofConeVecLaws.empty_bytes,bytesOf,List.map_nil,List.nil_append] at hm
  refine ⟨result,hr,hm,?_⟩
  have lengths := congrArg List.length hm
  change (bytesOf result.val).length = (expand (bytes.val.length/16) (bytesOf bytes.val)).length at lengths
  rw [expand_length (bytes.val.length/16) (bytesOf bytes.val) (by
    simp only [bytesOf,List.length_map]
    omega)] at lengths
  simp only [bytesOf,List.length_map] at lengths
  omega

#print axioms expand_length
#print axioms empty_accumulator
end AspisR1.MultiproofConeExpansionLength
