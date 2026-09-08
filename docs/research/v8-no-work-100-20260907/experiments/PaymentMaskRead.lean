import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! Source-shaped forest mask/read footprint. This proves invariance of all
raw witness fields for arbitrary mask assignments, not validator completeness.
No compiled trace equality or valid-witness premise is used. -/
set_option autoImplicit false
namespace AspisV8.PaymentMaskRead
def path (level : Nat) : Nat := 913 + 16*(level/4) + 4*(level%4)
def pathUsed (r c : Nat) : Prop :=
  ∃ l < 24, (r = path l ∧ c ≤ 8) ∨ r = path l + 1
def valueUsed (r c : Nat) : Prop :=
  (∃ v < 3, (r = 1008+2*v ∨ r = 1009+2*v ∨
    r = Nat.xor (1008+2*v) 12) ∧ c ≤ 10) ∨
  (r = 1014 ∧ c < 3) ∨ (r = 1015 ∧ c < 2)
def occupancyUsed (r c : Nat) : Prop :=
  (r = 1017 ∧ c ≤ 10) ∨ (r = 1018 ∧ c < 10)
/-- Within 1024x16: source forest path layout followed by the translated
legacy value/occupancy layout. Legacy private-path rows end before this tail. -/
def maskCell (r c : Nat) : Prop :=
  (r < 912 ∧ 13 ≤ r % 16) ∨
  (912 ≤ r ∧ ¬ ((r < 1008 ∧ pathUsed r c) ∨
    (1008 ≤ r ∧ (valueUsed r c ∨ occupancyUsed r c))))
def spongeRows : List Nat := [12,28,44,60,444,460,476,492,508,524]
/-- Over-approximates every value read by recovered_witness::decode:
all sixteen coordinates of the listed sponge rows, all ordered path children,
the direction bits, and the input occupancy pair. -/
def readCell (r c : Nat) : Prop :=
  (r ∈ spongeRows ∧ c < 16) ∨
  (∃ l < 24, (r = path l ∧ c = 0) ∨ (r = path l + 1 ∧ c < 16)) ∨
  (r = 1017 ∧ c < 2)

theorem path_bounds (l : Nat) (h : l < 24) :
    912 ≤ path l ∧ path l + 1 < 1008 := by
  unfold path
  omega

theorem sponge_bounds (r : Nat) (h : r ∈ spongeRows) :
    r < 912 ∧ r % 16 = 12 := by
  simp only [spongeRows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h <;> subst r <;> norm_num

theorem read_not_mask (r c : Nat) (h : readCell r c) : ¬ maskCell r c := by
  rcases h with ⟨hr,hc⟩ | ⟨l,hl,hr⟩ | ⟨hr,hc⟩
  · obtain ⟨hb,hm⟩ := sponge_bounds r hr
    simp only [maskCell]
    omega
  · obtain ⟨lo,hi⟩ := path_bounds l hl
    rcases hr with ⟨rfl,rfl⟩ | ⟨rfl,hc⟩
    · have used : pathUsed (path l) 0 := ⟨l,hl,Or.inl ⟨rfl,by omega⟩⟩
      simp only [maskCell]
      intro hm
      rcases hm with ⟨h,_⟩ | ⟨_,h⟩
      · omega
      · exact h (Or.inl ⟨by omega,used⟩)
    · have used : pathUsed (path l+1) c := ⟨l,hl,Or.inr rfl⟩
      simp only [maskCell]
      intro hm
      rcases hm with ⟨h,_⟩ | ⟨_,h⟩
      · omega
      · exact h (Or.inl ⟨hi,used⟩)
  · subst r
    have used : occupancyUsed 1017 c := Or.inl ⟨rfl,by omega⟩
    simp only [maskCell]
    intro hm
    rcases hm with ⟨h,_⟩ | ⟨_,h⟩
    · omega
    · exact h (Or.inr ⟨by omega,Or.inr used⟩)

noncomputable def applyMasks {F : Type*} [Add F]
    (table delta : Nat → Nat → F) (r c : Nat) : F := by
  classical
  exact if maskCell r c then table r c + delta r c else table r c

theorem all_decoder_reads_unchanged {F : Type*} [Add F]
    (table delta : Nat → Nat → F) (r c : Nat) (h : readCell r c) :
    applyMasks table delta r c = table r c := by
  classical
  unfold applyMasks
  exact if_neg (read_not_mask r c h)

def digest {F : Type*} (table : Nat → Nat → F) (row start : Nat) : Fin 8 → F :=
  fun i => table row (start+i.val)

theorem owner_key_mask_invariant {F : Type*} [Add F] (t d : Nat → Nat → F) :
    digest (applyMasks t d) 12 0 = digest t 12 0 := by
  funext i
  apply all_decoder_reads_unchanged
  left
  constructor
  · simp [spongeRows]
  · omega

theorem ordered_children_mask_invariant {F : Type*} [Add F]
    (t d : Nat → Nat → F) (l : Nat) (hl : l < 24) (side : Nat) (hs : side < 2) :
    digest (applyMasks t d) (path l+1) (8*side) =
      digest t (path l+1) (8*side) := by
  funext i
  apply all_decoder_reads_unchanged
  exact Or.inr (Or.inl ⟨l,hl,Or.inr ⟨rfl,by omega⟩⟩)

/-- These literal path-order residuals force the selected child to equal the
current digest. The sibling decoder selects the other child, including zero
coordinates. This is not a hash-preimage or path-root theorem. -/
theorem selected_child_of_residuals {F : Type*} [Field F]
    (bit current left right : F)
    (boolean : bit*(bit-1)=0)
    (leftResidual : (1-bit)*(left-current)=0)
    (rightResidual : bit*(right-current)=0) :
    (bit=0 ∧ left=current) ∨ (bit=1 ∧ right=current) := by
  rcases mul_eq_zero.mp boolean with h|h
  · left
    refine ⟨h, ?_⟩
    exact sub_eq_zero.mp (by simpa [h] using leftResidual)
  · have h1 : bit=1 := sub_eq_zero.mp h
    right
    refine ⟨h1, ?_⟩
    exact sub_eq_zero.mp (by simpa [h1] using rightResidual)

#print axioms read_not_mask
#print axioms all_decoder_reads_unchanged
#print axioms owner_key_mask_invariant
#print axioms ordered_children_mask_invariant
#print axioms selected_child_of_residuals
end AspisV8.PaymentMaskRead
