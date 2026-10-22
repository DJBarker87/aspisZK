import AspisR1PublicNonce41.Funs
import R1Z.ProverCommitArrayIndex25
import Mathlib.Tactic

/-! Symbolic byte-array zero test. No array value or seed carrier is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnerZero42
open Aeneas Aeneas.Std Result AspisR1PublicNonce41
attribute [local instance] Classical.propDecidable
abbrev Bytes := Aeneas.Std.Array U8 32#usize

def getByte (bytes : Bytes) (j : Fin 32) : U8 :=
  bytes.val[j.val]'(by have := bytes.property; change bytes.val.length = 32 at this; omega)

def zeroFrom (bytes : Bytes) (index : Nat) : Prop :=
  ∀ j : Fin 32, index ≤ j.val → getByte bytes j = 0#u8

theorem next_index (i : U8) (bound : i.val < 32) :
    (U8.wrapping_add i 1#u8).val = i.val+1 := by
  rw [U8.wrapping_add_val_eq]
  simp only [UScalar.size_def,UScalarTy.U8_numBits_eq,show (1#u8).val=1 from rfl]
  change (i.val+1)%256 = i.val+1
  exact Nat.mod_eq_of_lt (by omega)

theorem zero_from (bytes : Bytes) (n : Nat) (index : U8)
    (count : index.val+n=32) :
    owner.zero bytes index = ok (decide (zeroFrom bytes index.val)) := by
  induction n generalizing index with
  | zero =>
    have stop : index >= 32#u8 := by change 32 ≤ index.val; omega
    have all : zeroFrom bytes index.val := by intro j hj; have := j.isLt; omega
    rw [owner.zero]
    simp only [stop,if_true,all,decide_true]
  | succ n ih =>
    have bound : index.val < 32 := by omega
    have go : ¬ index >= 32#u8 := by change ¬ 32 ≤ index.val; omega
    let pos : Usize := UScalar.cast .Usize index
    have pv : pos.val = index.val := by dsimp [pos]; scalar_tac
    have read := ProverCommitArrayIndex25.array_index_usize_ok bytes pos
      (by change pos.val < 32; omega)
    have elem : bytes.val[pos.val]'(by have := bytes.property; change bytes.val.length=32 at this; omega) =
        getByte bytes ⟨index.val,bound⟩ := by simp only [getByte,pv]
    have step := ih (U8.wrapping_add index 1#u8) (by rw [next_index index bound]; omega)
    have split : zeroFrom bytes index.val ↔
        getByte bytes ⟨index.val,bound⟩ = 0#u8 ∧ zeroFrom bytes (index.val+1) := by
      constructor
      · intro h; exact ⟨h _ (le_refl _),fun j hj => h j (by omega)⟩
      · rintro ⟨h,t⟩ j hj
        by_cases eq : j.val=index.val
        · have je : j = ⟨index.val,bound⟩ := Fin.ext eq
          simpa only [je] using h
        · exact t j (by omega)
    rw [owner.zero]
    simp only [go,if_false,lift,bind_tc_ok]
    change (do let b ← Aeneas.Std.Array.index_usize bytes pos
               if b != 0#u8 then ok false
               else owner.zero bytes (U8.wrapping_add index 1#u8)) = _
    rw [read]
    simp only [bind_tc_ok,elem]
    by_cases hz : getByte bytes ⟨index.val,bound⟩ = 0#u8
    · have allEq : zeroFrom bytes index.val ↔ zeroFrom bytes (index.val+1) := by simp only [split,hz,true_and]
      simp only [hz,bne_self_eq_false,Bool.false_eq_true,if_false,step,next_index index bound,allEq]
    · have notAll : ¬ zeroFrom bytes index.val := fun h => hz (h _ (le_refl _))
      simp [hz,notAll]

theorem zero_spec (bytes : Bytes) :
    owner.zero bytes 0#u8 = ok (decide (∀ j, getByte bytes j = 0#u8)) := by
  simpa only [zeroFrom,show (0#u8).val=0 from rfl,Nat.zero_le,forall_const] using
    zero_from bytes 32 0#u8 (by rfl)

#print axioms next_index
#print axioms zero_from
#print axioms zero_spec
end R1Z.ProverCommitOwnerZero42
