import NLM_CheckedExtent
set_option autoImplicit false
noncomputable section
namespace NLM_CheckedAddFacts
open Aeneas Aeneas.Std AspisR1.S2W_D189Entry
/-- Natural checked-add fact obtained from the actual emitted std operation,
not a separately selected arithmetic equality. -/
theorem success (a b c : Usize) (returned : Usize.checked_add a b=some c) :
 c.val=a.val+b.val := by
 change Option.ofResult (Result.ofOption (UScalar.tryMkOpt .Usize (a.val+b.val)) .integerOverflow)=some c at returned
 unfold UScalar.tryMkOpt at returned
 split at returned
 · simp only [Result.ofOption,Option.ofResult] at returned
   cases returned
   rfl
 · cases returned
/-- The source's actual `data.len() != proof_end` false arm supplies equality. -/
theorem guard_eq (bytes : Slice U8) (end_ : Usize)
 (entered : (Slice.len bytes != end_)=false) : Slice.len bytes=end_ := by
 have same : (Slice.len bytes == end_)=true := by
   cases h : (Slice.len bytes == end_) <;> simp_all [bne]
 exact eq_of_beq same
/-- Actual SAME getter return, checked_add return, and length-test arm derive
57607. There is no free snapshot-length or checked-natural-sum premise. -/
theorem proof_length (ops : AdapterRw.Ops) (e : Entry) (bytes : Slice U8)
 (end_ length : Usize)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
  (e.snapshot 0 58295 58295)=.ok (.Ok bytes))
 (checked : Usize.checked_add 688#usize length=some end_)
 (guard : (Slice.len bytes != end_)=false) : length.val=57607 := by
 apply NLM_CheckedExtent.proof_length ops e bytes end_ length read (guard_eq bytes end_ guard)
 exact success 688#usize length end_ checked
#print success
#print guard_eq
#print proof_length
#print axioms success
#print axioms guard_eq
#print axioms proof_length
end NLM_CheckedAddFacts
