import R1Z.ProverCommitPack25
/-! Unequal-length version: the following packed stream can contain several
searches, so three independent five-word windows fit one fifteen-word source
stream without gaps after early success. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPackWindows25
open R0Z R0Z.FsAbort R1Z.CouplingR1PBin ProverCommitPack25
attribute [local instance] Classical.propDecidable
variable {A : Type} (zero : A)
def pack {n m : Nat} (tapes : (Fin n → A) × (Fin m → A)) : Fin (n+m) → A :=
  let c := used zero tapes.1
  fun i => if h : i.val < c then tapes.1 ⟨i.val,by have hc:=used_le zero tapes.1;omega⟩
    else if h₂ : i.val < c+m then tapes.2 ⟨i.val-c,by omega⟩
    else tapes.1 ⟨i.val-m,by have hi:=i.isLt;omega⟩

def front {n m : Nat} (stream : Fin (n+m) → A) : Fin n → A :=
  fun i => stream ⟨i.val,by have hi:=i.isLt;omega⟩

def unpack {n m : Nat} (stream : Fin (n+m) → A) : (Fin n → A) × (Fin m → A) :=
  let c := used zero (front (n := n) (m := m) stream)
  ((fun i => if h : i.val < c then stream ⟨i.val,by have hi:=i.isLt;omega⟩
    else stream ⟨i.val+m,by have hi:=i.isLt;omega⟩),
   fun i => stream ⟨c+i.val,by have hc:=used_le zero (front (n := n) (m := m) stream);have hi:=i.isLt;omega⟩)

theorem used_pack {n m : Nat} (tapes : (Fin n → A) × (Fin m → A)) :
    used zero (front (n := n) (m := m) (pack zero tapes)) = used zero tapes.1 := by
  apply used_prefix
  intro i hi
  simp only [front,pack]
  rw [dif_pos hi]

theorem used_unpack {n m : Nat} (stream : Fin (n+m) → A) :
    used zero (unpack zero stream).1 = used zero (front (n := n) (m := m) stream) := by
  apply used_prefix
  intro i hi
  simp only [unpack]
  rw [dif_pos hi]
  rfl

theorem unpack_pack {n m : Nat} (tapes : (Fin n → A) × (Fin m → A)) :
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
    have h₂ : used zero tapes.1 + i.val < used zero tapes.1+m := by have h:=i.isLt;omega
    rw [dif_neg h₁,dif_pos h₂]
    apply congrArg tapes.2
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

theorem pack_unpack {n m : Nat} (stream : Fin (n+m) → A) :
    pack zero (unpack zero stream) = stream := by
  funext i
  simp only [pack,used_unpack]
  by_cases h₁ : i.val < used zero (front (n := n) (m := m) stream)
  · rw [dif_pos h₁]
    simp only [unpack]
    rw [dif_pos h₁]
  · rw [dif_neg h₁]
    by_cases h₂ : i.val < used zero (front (n := n) (m := m) stream)+m
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

def equiv (n m : Nat) : ((Fin n → A) × (Fin m → A)) ≃ (Fin (n+m) → A) where
  toFun := pack zero
  invFun := unpack zero
  left_inv := unpack_pack zero
  right_inv := pack_unpack zero

/-- The whole persistent stream is exactly uniform, even though its window
boundary is chosen by the preceding rejection answers. -/
theorem packed_uniform [Fintype A] (n m : Nat) : MP (pack zero (n := n) (m := m)) := mp_equiv (equiv zero n m)

#print axioms used_pack
#print axioms used_unpack
#print axioms unpack_pack
#print axioms pack_unpack
#print axioms packed_uniform
end R1Z.ProverCommitPackWindows25
