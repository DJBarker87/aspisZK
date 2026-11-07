import NMO_PrefixRegion
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_PrefixEmbedding
open Aeneas Aeneas.Std Result
/-- Extending unused buffer suffixes preserves every original checked window. -/
theorem slice_append (xs ys : List U8) (lo hi : Nat)
 (ordered : lo≤hi) (bound : hi≤xs.length) :
 List.slice lo hi (xs++ys)=List.slice lo hi xs := by
 have low : lo≤xs.length := by omega
 have width : hi-lo≤xs.length-lo := by omega
 simp only [List.slice,List.drop_append,List.take_append,List.length_drop,
  Nat.sub_eq_zero_of_le low,Nat.sub_eq_zero_of_le bound,Nat.sub_eq_zero_of_le width,
  List.drop_zero,List.take_zero,List.append_nil,List.drop_nil,List.take_nil]
/-- The independent-start native envelope represents every caller Prefix
value. It does not assert native correspondence for any parent invocation. -/
theorem represented {H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input) :
 ∃ buffer : List U8,buffer.length=57575 ∧
 ∀ frame∈input.prefix1.records.val,∃ start : Nat,
 start≤57575 ∧ frame.val.length≤57575-start ∧
 frame.val=List.slice start (start+frame.val.length) buffer := by
 obtain ⟨bytes,extent,windows⟩ := NMO_PrefixRegion.source input domain
 let padding := List.replicate (57575-bytes.val.length) (0#u8)
 let buffer := bytes.val++padding
 refine ⟨buffer,?_,?_⟩
 · simp only [buffer,padding,List.length_append,List.length_replicate]
   omega
 · intro frame member
   obtain ⟨start,bound,same⟩ := windows frame member
   refine ⟨start,by omega,by omega,?_⟩
   calc frame.val=List.slice start (start+frame.val.length) bytes.val := same
        _=List.slice start (start+frame.val.length) buffer :=
         (slice_append bytes.val padding start (start+frame.val.length) (by omega) bound).symm
#print axioms slice_append
#print axioms represented
set_option pp.proofs false in #print represented
end AspisR1.NMO_PrefixEmbedding
end
