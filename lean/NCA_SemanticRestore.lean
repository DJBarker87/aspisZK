import NBR_BufferJoin
set_option autoImplicit false
namespace AspisR1.NCA_SemanticRestore
open Aeneas Aeneas.Std Result

/-- The real mutable-borrow restoration operation on the ORIGINAL full logical
carrier, rather than a separately fabricated successful prepare output. -/
theorem source (logical semantic : Slice U8) (full : logical.val.length=14759)
    (size : semantic.val.length=13831) :
    (logical.val.setSlice! 0 semantic.val) = semantic.val++logical.val.drop 13831 := by
  simp only [List.setSlice!,List.take_zero,List.nil_append,Nat.zero_add,size]
  have count : min 13831 (logical.val.length-0)=13831 := by omega
  rw [count,←size,List.take_length]

#print axioms source
end AspisR1.NCA_SemanticRestore
