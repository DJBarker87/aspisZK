import PV_LIB_SPEC_LaneA_A_OwnerStore
import PV_LIB_A_C18_A_Range165
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeWriter
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_THR2_SourceStoreLibrary
/-- f15's source Range receiver is local7. The source typed reference and the
source aggregate constructor determine the write; no write-definedness or
pointer-layout environment premise is accepted. Caller history must establish
this local cell, including the preceding exact165 value law. -/
theorem range93 (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (w : OWNER)
    (a start finish : Nat) (metadata : Data)
    (cell : s.cells ⟨a,7,[]⟩ = some (PV_LIB_A_Range165.sourceRange start finish)) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    PV_THR2_LibrarySemantics_RangeNext93 B
      [PV_STX2_TypedReferences.reference ⟨a,7,[]⟩ metadata] s w =
      some (if start < finish then
        write s ⟨a,7,[]⟩ (some (PV_LIB_A_Range165.sourceRange (start+1) finish)) else s) := by
  intro B
  have address : B.dereference w
      (PV_STX2_TypedReferences.reference ⟨a,7,[]⟩ metadata) = some ⟨a,7,[]⟩ := by rfl
  have received : PV_THR2_SourceStoreLibrary.receiver B s w
      (PV_STX2_TypedReferences.reference ⟨a,7,[]⟩ metadata) =
        some (⟨a,7,[]⟩,PV_LIB_A_Range165.sourceRange start finish) := by
    unfold PV_THR2_SourceStoreLibrary.receiver
    rw [address]
    have read : readAddress B s ⟨a,7,[]⟩ =
        some (PV_LIB_A_Range165.sourceRange start finish) := by
      change (s.cells ⟨a,7,[]⟩).bind (readFields B []) = _
      rw [cell]
      rfl
    change (readAddress B s ⟨a,7,[]⟩).bind
      (fun value => some ((⟨a,7,[]⟩ : Address),value)) = _
    rw [read]
    rfl
  dsimp only [PV_THR2_LibrarySemantics_RangeNext93]
  rw [received]
  change (if start < finish then
    writeAddress B s (withField ⟨a,7,[]⟩ 0) (some (.number (start+1))) else some s) = _
  by_cases live : start < finish
  · simp only [if_pos live]
    unfold writeAddress
    change (s.cells ⟨a,7,[]⟩).bind _ = _
    rw [cell]
    rfl
  · simp only [if_neg live]
#print axioms range93
end PV_LIB_A_RangeWriter
