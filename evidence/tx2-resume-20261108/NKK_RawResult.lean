import NKK_RawPrefix
set_option autoImplicit false
noncomputable section
namespace NKK_RawResult
open Aeneas Aeneas.Std Result NKK_NativeRaw

/-- The native raw-prefix result is this exact bounded Reader chain. -/
theorem source (n : Usize) (count : Nat) (r : Reader) :
 (NKK_RawPrefix.literal n count r).result=reads n count r := by
 induction count generalizing r with
 | zero => rfl
 | succ count ih =>
  unfold NKK_RawPrefix.literal reads
  simp only [NJU_Log.erase_bind,NJU_Log.erase_pure,NJU_ResumeObserved.recordRaw,NJU_Log.erase_record]
  apply NIL_ResultCases.bind_congr
  rintro ⟨bytes,next⟩
  rw [ih]
  apply NIL_ResultCases.bind_congr
  rintro ⟨tail,last⟩
  rfl

#print axioms source
end NKK_RawResult
