import S2TrustedSdkBorrow

/-! Symbolic byte footprint, arbitrary widths; no concrete recurrence reduction.
Native binding is a separate obligation. `s` is the copy cut of ONE execution.
The source function is a snapshot at that cut, not a post-native buffer read. -/
set_option autoImplicit false
namespace AspisR1.S2C
open S2Trust

def copyPrefix {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8) : Nat → Heap F
  | 0 => s
  | n+1 => writeAt (copyPrefix s g source n) g n (source n)

/-- Account records, lamports/Rc/allocator/oracle ambient state and allocation
geometry are unchanged by element writes. No allocator law is assumed here. -/
theorem copy_structural_frame {F : Type} (s : Heap F) (g : Guard)
    (source : Nat → UInt8) (n : Nat) :
    (copyPrefix s g source n).accounts = s.accounts ∧
    (copyPrefix s g source n).ownerLive = s.ownerLive ∧
    (copyPrefix s g source n).allocated = s.allocated ∧
    (copyPrefix s g source n).counter = s.counter ∧
    (copyPrefix s g source n).external = s.external ∧
    (copyPrefix s g source n).guards = s.guards ∧
    (copyPrefix s g source n).ambient = s.ambient := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih => exact ih

theorem copy_descriptor {F : Type} (s : Heap F) (g : Guard)
    (source : Nat → UInt8) (n c : Nat) :
    ((copyPrefix s g source n).payload c).descriptor = (s.payload c).descriptor := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [copyPrefix, writeAt, put]
    split <;> simp_all only

theorem copy_other_cell {F : Type} (s : Heap F) (g : Guard)
    (source : Nat → UInt8) (n c : Nat) (different : c ≠ g.cell) :
    (copyPrefix s g source n).payload c = s.payload c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [copyPrefix,writeAt,put,if_neg different] using ih

theorem copy_exact_byte {F : Type} (s : Heap F) (g : Guard)
    (source : Nat → UInt8) (n i : Nat) :
    ((copyPrefix s g source n).payload g.cell).contents i =
      if i < n then source i else (s.payload g.cell).contents i := by
  induction n with
  | zero => simp only [copyPrefix, Nat.not_lt_zero, if_false]
  | succ n ih =>
    simp only [copyPrefix,writeAt,put,eq_self_iff_true,ite_true]
    by_cases eq : i = n
    · subst i; simp only [eq_self_iff_true, Nat.lt_succ_self, ite_true]
    · rw [if_neg eq, ih]
      by_cases lt : i < n
      · rw [if_pos lt, if_pos (Nat.lt.step lt)]
      · have no : ¬ i < n+1 := by omega
        rw [if_neg lt, if_neg no]

/-- Native :985 has offset zero and copies the whole accepted CP length.
This theorem does not assume account keys establish cell separation. -/
theorem checkpoint_copy_regions {F : Type} (s : Heap F) (g : Guard)
    (source : Nat → UInt8) (proof pubCell : Nat)
    (proofSeparate : proof ≠ g.cell) (publicSeparate : pubCell ≠ g.cell) :
    (∀ i, i < 1768 → ((copyPrefix s g source 1768).payload g.cell).contents i = source i) ∧
    (copyPrefix s g source 1768).payload proof = s.payload proof ∧
    (copyPrefix s g source 1768).payload pubCell = s.payload pubCell ∧
    (∀ c, ((copyPrefix s g source 1768).payload c).descriptor = (s.payload c).descriptor) := by
  exact ⟨fun i hi => (copy_exact_byte s g source 1768 i).trans (if_pos hi),
    copy_other_cell s g source 1768 proof proofSeparate,
    copy_other_cell s g source 1768 pubCell publicSeparate,
    copy_descriptor s g source 1768⟩

#print axioms copy_structural_frame
#print axioms copy_descriptor
#print axioms copy_other_cell
#print axioms copy_exact_byte
#print axioms checkpoint_copy_regions
end AspisR1.S2C
