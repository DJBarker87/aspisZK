import NCX_WindowFrames
set_option autoImplicit false
namespace NCX_CallerDomains
open Aeneas Aeneas.Std Result AspisR1

theorem registry_array (b : Slice U8) (len : b.val.length=256) (off : Nat)
    (member : off ∈ NCX_WindowFrames.registryStarts) : off+32 ≤ b.val.length := by
  simp only [NCX_WindowFrames.registryStarts,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h <;> omega
theorem entry_array (b : Slice U8) (len : b.val.length=320) (off : Nat)
    (member : off ∈ NCX_WindowFrames.entryStarts) : off+32 ≤ b.val.length := by
  simp only [NCX_WindowFrames.entryStarts,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h <;> omega
theorem registry_word (b : Slice U8) (len : b.val.length=256) (off : Nat)
    (member : off=104 ∨ off=112) : off+8 ≤ b.val.length := by omega
theorem entry_word (b : Slice U8) (len : b.val.length=320) (off : Nat)
    (member : off=264 ∨ off=272) : off+8 ≤ b.val.length := by omega
theorem registry_byte (b : Slice U8) (len : b.val.length=256) (off : Nat)
    (member : off=4 ∨ off=5 ∨ off=6 ∨ off=7 ∨ off=248) : off<b.val.length := by omega
theorem entry_byte (b : Slice U8) (len : b.val.length=320) (off : Nat)
    (member : off=4 ∨ off=5 ∨ off=6 ∨ off=7 ∨ off=312 ∨ off=313) : off<b.val.length := by omega

theorem registry_reserved (b : Slice U8) (len : b.val.length=256) :
    (JHg_FieldRead.segment b 249 7).val.length=7 ∧
    (JHg_FieldRead.segment b 249 7).val.length ≤ 768 := by
  have h:=JHg_FieldRead.length b 249 7 (by omega)
  exact ⟨h,by omega⟩
theorem entry_reserved (b : Slice U8) (len : b.val.length=320) :
    (JHg_FieldRead.segment b 314 6).val.length=6 ∧
    (JHg_FieldRead.segment b 314 6).val.length ≤ 768 := by
  have h:=JHg_FieldRead.length b 314 6 (by omega)
  exact ⟨h,by omega⟩
/-- Every validation binding scan satisfies the reused induction's cap. -/
theorem binding_scan (a : Array U8 32#usize) : a.to_slice.val.length ≤ 768 := by
  change a.val.length ≤ 768
  rw [a.property]
  scalar_tac
#print axioms registry_array
#print axioms entry_array
#print axioms registry_word
#print axioms entry_word
#print axioms registry_byte
#print axioms entry_byte
#print axioms registry_reserved
#print axioms entry_reserved
#print axioms binding_scan
end NCX_CallerDomains
