import Port4B_SlotInstall

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_NodeViews
open Aeneas Aeneas.Std Result

/-- Value image of the fixed source borrow; no native copy is introduced. -/
def view (proof : Slice U8) (batch kind : Nat) : Slice U8 :=
  ⟨(proof.val.drop (OraclePortSelectedDraft.slotStart (3*batch+kind))).take
      (32*OraclePortSelectedDraft.capacity (3*batch+kind)),by
    have := proof.property
    simp only [List.length_take,List.length_drop]
    omega⟩

/-- The existing checked source range constructs this SAME proof view. -/
theorem source (proof : Slice U8) (size : proof.val.length = 57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val)
    (batch kind : Nat) (bb : batch < 2) (kb : kind < 3) (slot : Usize) (index : slot.val = 3*batch+kind) :
    Port4B_SlotInstall.nodeSlot proof slot = ok (view proof batch kind) ∧
    (view proof batch kind).val.length = 32*OraclePortSelectedDraft.capacity (3*batch+kind) := by
  obtain ⟨actual,read,len,bytes⟩ := Port4B_SlotInstall.physical proof size parsed wire batch kind bb kb slot index
  have expected : MultiproofConeCanonical.bytesOf (view proof batch kind).val =
      OraclePortCompactDraft.slice parsed.wire (OraclePortSelectedDraft.slotStart (3*batch+kind))
        (32*OraclePortSelectedDraft.capacity (3*batch+kind)) := by
    simp only [view,wire,MultiproofConeCanonical.bytesOf,OraclePortCompactDraft.slice,List.map_take,List.map_drop]
  have same : actual = view proof batch kind := Subtype.ext
    (MultiproofConeByteEquality.bytes_injective (bytes.trans expected.symm))
  subst actual
  exact ⟨read,len⟩

/-- All six actual capacities fit the native row and slice domains. -/
theorem capacity (batch kind : Nat) (bb : batch < 2) (kb : kind < 3) :
    OraclePortSelectedDraft.capacity (3*batch+kind) ≤ 172 := by
  interval_cases batch <;> interval_cases kind <;> decide

#print axioms source
#print axioms capacity
end AspisR1.NCM_NodeViews
end
