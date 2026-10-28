import R1Z.ProverCommitProduct25
/-! Pack independent search windows into a persistent source stream. Keep
only the first search's consumed front before the next window, moving its
unused suffix behind that next window. The value-dependent packing is a
bijection, not an arbitrary value-dependent permutation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPack25
open R0Z R0Z.FsAbort R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable
variable {A : Type} (zero : A)

def used : {n : Nat} → (Fin n → A) → Nat
  | 0, _ => 0
  | _+1, tape => if tape 0 = zero then 1 + used (fun i => tape i.succ) else 1

theorem used_le {n : Nat} (tape : Fin n → A) : used zero tape ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [used]
    split
    · have h := ih (fun i => tape i.succ);omega
    · omega

/-- Later values cannot alter the number of words already consumed. -/
theorem used_prefix {n : Nat} (left right : Fin n → A)
    (front : ∀ i, i.val < used zero left → right i = left i) :
    used zero right = used zero left := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have positive : 0 < used zero left := by simp only [used];split <;> omega
    have head := front 0 positive
    by_cases h : left 0 = zero
    · have hr : right 0 = zero := head.trans h
      simp only [used,h,hr,if_true]
      congr 1
      apply ih
      intro i hi
      apply front i.succ
      simp only [used,h,if_true]
      have hv : i.succ.val=i.val+1 := rfl
      omega
    · have hr : right 0 ≠ zero := fun e => h (head.symm.trans e)
      simp only [used,h,hr,if_false]

def pack {n : Nat} (tapes : (Fin n → A) × (Fin n → A)) : Fin (n+n) → A :=
  let c := used zero tapes.1
  fun i => if h : i.val < c then tapes.1 ⟨i.val,by have hc:=used_le zero tapes.1;omega⟩
    else if h₂ : i.val < c+n then tapes.2 ⟨i.val-c,by omega⟩
    else tapes.1 ⟨i.val-n,by have hi:=i.isLt;omega⟩

def front {n : Nat} (stream : Fin (n+n) → A) : Fin n → A :=
  fun i => stream ⟨i.val,by have hi:=i.isLt;omega⟩

def unpack {n : Nat} (stream : Fin (n+n) → A) : (Fin n → A) × (Fin n → A) :=
  let c := used zero (front stream)
  ((fun i => if h : i.val < c then stream ⟨i.val,by have hi:=i.isLt;omega⟩
    else stream ⟨i.val+n,by have hi:=i.isLt;omega⟩),
   fun i => stream ⟨c+i.val,by have hc:=used_le zero (front stream);have hi:=i.isLt;omega⟩)

theorem used_pack {n : Nat} (tapes : (Fin n → A) × (Fin n → A)) :
    used zero (front (pack zero tapes)) = used zero tapes.1 := by
  apply used_prefix
  intro i hi
  simp only [front,pack]
  rw [dif_pos hi]

theorem used_unpack {n : Nat} (stream : Fin (n+n) → A) :
    used zero (unpack zero stream).1 = used zero (front stream) := by
  apply used_prefix
  intro i hi
  simp only [unpack]
  rw [dif_pos hi]
  rfl

theorem unpack_pack {n : Nat} (tapes : (Fin n → A) × (Fin n → A)) :
    unpack zero (pack zero tapes) = tapes := by
  apply Prod.ext
  · funext i
    simp only [unpack,used_pack]
    by_cases hi : i.val < used zero tapes.1
    · rw [dif_pos hi]
      simp only [pack]
      rw [dif_pos hi]
    · rw [dif_neg hi]
      simp only [pack]
      rw [dif_neg (by omega),dif_neg (by omega)]
      apply congrArg tapes.1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
  · funext i
    simp only [unpack,used_pack]
    simp only [pack]
    have h₁ : ¬ used zero tapes.1 + i.val < used zero tapes.1 := by omega
    have h₂ : used zero tapes.1 + i.val < used zero tapes.1+n := by have h:=i.isLt;omega
    rw [dif_neg h₁,dif_pos h₂]
    apply congrArg tapes.2
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

theorem pack_unpack {n : Nat} (stream : Fin (n+n) → A) :
    pack zero (unpack zero stream) = stream := by
  funext i
  simp only [pack,used_unpack]
  by_cases h₁ : i.val < used zero (front stream)
  · rw [dif_pos h₁]
    simp only [unpack]
    rw [dif_pos h₁]
  · rw [dif_neg h₁]
    by_cases h₂ : i.val < used zero (front stream)+n
    · rw [dif_pos h₂]
      simp only [unpack]
      apply congrArg stream
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    · rw [dif_neg h₂]
      simp only [unpack]
      rw [dif_neg (by omega)]
      apply congrArg stream
      apply Fin.ext
      simp only [Fin.val_mk]
      have h:=i.isLt
      omega

def equiv (n : Nat) : ((Fin n → A) × (Fin n → A)) ≃ (Fin (n+n) → A) where
  toFun := pack zero
  invFun := unpack zero
  left_inv := unpack_pack zero
  right_inv := pack_unpack zero

/-- The whole persistent stream is exactly uniform, even though its window
boundary is chosen by the preceding rejection answers. -/
theorem packed_uniform [Fintype A] (n : Nat) : MP (pack zero (n := n)) := mp_equiv (equiv zero n)

#print axioms used_le
#print axioms used_prefix
#print axioms used_pack
#print axioms used_unpack
#print axioms unpack_pack
#print axioms pack_unpack
#print axioms packed_uniform
end R1Z.ProverCommitPack25
