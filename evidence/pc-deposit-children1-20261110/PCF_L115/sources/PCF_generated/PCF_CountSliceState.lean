import PCF_CountSlice
import PCA_RowSpec_POOL_332
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_CountSliceState
/-- Finite reachable constructor carrier only; no arbitrary ProgramError ABI quotient. -/
def reply (tag : U8) : PCA.Outcome Unit :=
  if tag.val=0 then .ok ()
  else .error (.program (if tag.val=1 then PCA.notEnoughKeys else 2*2^32))

theorem complete {T : Type} (accounts : Slice T) (expected : Usize) (s : PCA.PCA_State)
    (same_count : s.accountCount=accounts.length) :
    ∃ out : U8, PCF_CountSliceRef.count_reference accounts expected = ok out ∧
      PCA.countReference expected.val s = ⟨s,[],reply out⟩ := by
  refine ⟨PCF_CountWord.tag (PCF_Count.source accounts.length expected.val),PCF_CountSlice.complete accounts expected,?_⟩
  by_cases he : accounts.length=expected.val <;>
    by_cases hl : accounts.length<expected.val <;>
      simp [PCA.countReference,same_count,PCF_Count.source,PCF_CountWord.tag,reply,he,hl]
#print axioms complete
end PCF_CountSliceState
