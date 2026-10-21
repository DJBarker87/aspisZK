import R1Z.SimCostTapeCoupling

/-! Fixed-width arithmetic batches in the existing primitive RAM tariff model.
The primitive semantics are exact M31/QM31 field operations. These are not a
Rust arithmetic refinement, nor an operation-count certificate for simE's
reference/mask/shift formulas. Lists are traversed explicitly. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostFixedOperations
open R1Z.SimCostWriter AspisV8R15.ExactTowerBase
attribute [local instance] Classical.propDecidable

/-- A primitive field instruction, charged according to the existing RAM
vocabulary. This definition is used only for the four fixed field operations
below, not to assign a cost to arbitrary metadata callbacks. -/
def m31Add : Stage (fun p : M31Exact × M31Exact => p.1+p.2) (tariff .m31Add) where
  run p := (p.1+p.2,tariff .m31Add)
  erase _ := rfl
  bound _ := Nat.le_refl _

def m31Mul : Stage (fun p : M31Exact × M31Exact => p.1*p.2) (tariff .m31Mul) where
  run p := (p.1*p.2,tariff .m31Mul)
  erase _ := rfl
  bound _ := Nat.le_refl _

def qm31Add : Stage (fun p : QM31Exact × QM31Exact => p.1+p.2) (tariff .qm31Add) where
  run p := (p.1+p.2,tariff .qm31Add)
  erase _ := rfl
  bound _ := Nat.le_refl _

def qm31Mul : Stage (fun p : QM31Exact × QM31Exact => p.1*p.2) (tariff .qm31Mul) where
  run p := (p.1*p.2,tariff .qm31Mul)
  erase _ := rfl
  bound _ := Nat.le_refl _

/-- Include one output-list insertion and one control tick per instruction. -/
def batch {A B : Type} {f : A → B} {c : Nat} (s : Stage f c) : List A → Costed (List B)
  | [] => ([],0)
  | a::tail =>
    let v := s.run a
    let rest := batch s tail
    (v.1::rest.1,v.2+rest.2+2)

theorem batch_erase {A B : Type} {f : A → B} {c : Nat}
    (s : Stage f c) (xs : List A) : (batch s xs).1 = xs.map f := by
  induction xs with
  | nil => rfl
  | cons a tail ih => simp only [batch, s.erase, ih, List.map_cons]

theorem batch_bound {A B : Type} {f : A → B} {c : Nat}
    (s : Stage f c) (xs : List A) : (batch s xs).2 ≤ xs.length*(c+2) := by
  induction xs with
  | nil => simp only [batch, List.length_nil, Nat.zero_mul, le_refl]
  | cons a tail ih =>
    have hv := s.bound a
    simp only [batch, List.length_cons]
    nlinarith

/-- Abstract stage packaging of the actual loop over a fixed-length list. -/
def fixedBatch {A B : Type} {f : A → B} {c : Nat} (s : Stage f c) (n : Nat) :
    Stage (fun xs : {xs : List A // xs.length = n} => xs.val.map f) (n*(c+2)) where
  run xs := batch s xs.val
  erase xs := batch_erase s xs.val
  bound xs := by simpa only [xs.property] using batch_bound s xs.val

theorem m31_add_batch (xs : List (M31Exact × M31Exact)) :
    (batch m31Add xs).1 = xs.map (fun p => p.1+p.2) ∧
    (batch m31Add xs).2 ≤ 3*xs.length := by
  refine ⟨batch_erase _ _, ?_⟩
  simpa only [tariff, Nat.mul_comm] using batch_bound m31Add xs

theorem m31_mul_batch (xs : List (M31Exact × M31Exact)) :
    (batch m31Mul xs).1 = xs.map (fun p => p.1*p.2) ∧
    (batch m31Mul xs).2 ≤ 3*xs.length := by
  refine ⟨batch_erase _ _, ?_⟩
  simpa only [tariff, Nat.mul_comm] using batch_bound m31Mul xs

theorem qm31_add_batch (xs : List (QM31Exact × QM31Exact)) :
    (batch qm31Add xs).1 = xs.map (fun p => p.1+p.2) ∧
    (batch qm31Add xs).2 ≤ 6*xs.length := by
  refine ⟨batch_erase _ _, ?_⟩
  simpa only [tariff, Nat.mul_comm] using batch_bound qm31Add xs

theorem qm31_mul_batch (xs : List (QM31Exact × QM31Exact)) :
    (batch qm31Mul xs).1 = xs.map (fun p => p.1*p.2) ∧
    (batch qm31Mul xs).2 ≤ 34*xs.length := by
  refine ⟨batch_erase _ _, ?_⟩
  simpa only [tariff, Nat.mul_comm] using batch_bound qm31Mul xs

/-- A batch no larger than the proved protocol coordinate envelope. This
bounds such a batch; it does not assert simE uses only one such batch. -/
theorem protocol_sized_batch {A B : Type} {f : A → B} {c : Nat}
    (s : Stage f c) (xs : List A)
    (hlen : xs.length ≤ Fintype.card SimCostTapeCoupling.Coordinates) :
    (batch s xs).2 ≤ 417792*(c+2) := by
  exact (batch_bound s xs).trans
    (Nat.mul_le_mul_right _ (hlen.trans SimCostTapeCoupling.sample_count))

#print axioms batch_erase
#print axioms batch_bound
#print axioms m31_add_batch
#print axioms m31_mul_batch
#print axioms qm31_add_batch
#print axioms qm31_mul_batch
#print axioms protocol_sized_batch
end R1Z.SimCostFixedOperations
