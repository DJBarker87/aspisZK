import NCX_FieldLaws
import NCV_CopyFrame
set_option autoImplicit false
namespace NCX_WindowFrames
open Aeneas Aeneas.Std Result AspisR1

/-- Only the selected 32 bytes affect the reference array read. -/
theorem read32_local (b c : Slice U8) (p q : Usize)
    (bp : p.val+32 ≤ b.val.length) (cq : q.val+32 ≤ c.val.length)
    (same : (b.val.drop p.val).take 32=(c.val.drop q.val).take 32) :
    NCX_Reference.read32 b p=NCX_Reference.read32 c q := by
  let a : Array U8 32#usize := ⟨(b.val.drop p.val).take 32,by
    simp only [List.length_take,List.length_drop,show (32#usize).val=32 from rfl];omega⟩
  rw [NCX_FieldLaws.read32 b p a bp rfl,NCX_FieldLaws.read32 c q a cq same.symm]

/-- The same locality law for an eight-byte word; ambient bytes are unrestricted. -/
theorem word_local (b c : Slice U8) (p q : Usize)
    (bp : p.val+8 ≤ b.val.length) (cq : q.val+8 ≤ c.val.length)
    (same : (b.val.drop p.val).take 8=(c.val.drop q.val).take 8) :
    NCX_Reference.word b p=NCX_Reference.word c q := by
  let a : Array U8 8#usize := ⟨(b.val.drop p.val).take 8,by
    simp only [List.length_take,List.length_drop,show (8#usize).val=8 from rfl];omega⟩
  rw [NCX_FieldLaws.word b p a bp rfl,NCX_FieldLaws.word c q a cq same.symm]

def registryStarts : List Nat := [8,40,72,120,152,184,216]
def entryStarts : List Nat := [8,40,72,104,136,168,200,232,280]

theorem registry_disjoint (i j : Nat) (hi : i ∈ registryStarts)
    (hj : j ∈ registryStarts) (order : i<j) : i+32 ≤ j := by
  simp only [registryStarts,List.mem_cons,List.not_mem_nil,or_false] at hi hj
  rcases hi with h|h|h|h|h|h|h <;> rcases hj with g|g|g|g|g|g|g <;> omega
theorem entry_disjoint (i j : Nat) (hi : i ∈ entryStarts)
    (hj : j ∈ entryStarts) (order : i<j) : i+32 ≤ j := by
  simp only [entryStarts,List.mem_cons,List.not_mem_nil,or_false] at hi hj
  rcases hi with h|h|h|h|h|h|h|h|h <;> rcases hj with g|g|g|g|g|g|g|g|g <;> omega

/-- Exact KMX value laws. Pointer/caller association is not asserted here. -/
theorem registry_commute {A : Type} (read old : Nat → A) (i j : Nat)
    (hi : i ∈ registryStarts) (hj : j ∈ registryStarts) (order : i<j) :
    KMX_CopyMeaning.loop read (KMX_CopyMeaning.loop read old i 32) j 32=
    KMX_CopyMeaning.loop read (KMX_CopyMeaning.loop read old j 32) i 32 :=
  NCV_CopyFrame.commute read read old i 32 j 32 (Or.inl (registry_disjoint i j hi hj order))
theorem entry_commute {A : Type} (read old : Nat → A) (i j : Nat)
    (hi : i ∈ entryStarts) (hj : j ∈ entryStarts) (order : i<j) :
    KMX_CopyMeaning.loop read (KMX_CopyMeaning.loop read old i 32) j 32=
    KMX_CopyMeaning.loop read (KMX_CopyMeaning.loop read old j 32) i 32 :=
  NCV_CopyFrame.commute read read old i 32 j 32 (Or.inl (entry_disjoint i j hi hj order))

def fields {A : Type} (read old : Nat → A) : List Nat → Nat → A
  | [] => old
  | off::rest => KMX_CopyMeaning.loop read (fields read old rest) off 32

theorem outside {A : Type} (read old : Nat → A) (offsets : List Nat) (k : Nat)
    (separate : ∀ off ∈ offsets, k<off ∨ off+32 ≤ k) :
    fields read old offsets k=old k := by
  induction offsets with
  | nil => rfl
  | cons off rest ih =>
    rw [fields,NCV_CopyFrame.outside _ _ _ _ _ (separate off (List.mem_cons_self ..))]
    apply ih
    intro start member
    exact separate start (List.mem_cons_of_mem off member)
#print axioms read32_local
#print axioms word_local
#print axioms registry_disjoint
#print axioms entry_disjoint
#print axioms registry_commute
#print axioms entry_commute
#print axioms outside
end NCX_WindowFrames
