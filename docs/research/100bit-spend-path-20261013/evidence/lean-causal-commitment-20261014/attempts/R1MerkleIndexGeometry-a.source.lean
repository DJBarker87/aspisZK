import R1Merkle32Path
import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-! Mixed-radix indexing facts for six eight-way Merkle levels and the folded
query index. These are arithmetic definitions only, with no source semantics. -/
set_option autoImplicit false
namespace AspisR1.MerkleIndexGeometry

open AspisR1.Merkle32Path

def slots : Nat → Nat → List (Fin 8)
  | 0, _ => []
  | depth + 1, i =>
      ⟨i % 8, Nat.mod_lt _ (by omega)⟩ :: slots depth (i / 8)

def index : List (Fin 8) → Nat
  | [] => 0
  | slot :: rest => slot.val + 8 * index rest

theorem length_slots (depth i : Nat) : (slots depth i).length = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [slots, ih]

theorem index_slots (depth i : Nat) (hi : i < 8 ^ depth) :
    index (slots depth i) = i := by
  induction depth generalizing i with
  | zero =>
      simp [slots, index] at hi ⊢
  | succ depth ih =>
      have hdiv : i / 8 < 8 ^ depth := by
        rw [pow_succ] at hi
        omega
      have hrec := ih (i / 8) hdiv
      simp only [slots, index]
      rw [hrec]
      have hmoddiv := Nat.mod_add_div i 8
      omega

def foldedIndex (u : Fin 262144) : Fin 65536 :=
  ⟨u.val / 4, by omega⟩

theorem foldedIndex_decompose (u : Fin 262144) :
    u.val = 4 * (foldedIndex u).val + u.val % 4 := by
  have hmoddiv := Nat.mod_add_div u.val 4
  simp only [foldedIndex]
  omega

theorem slots6_injective : Function.Injective (fun u : Fin 262144 => slots 6 u.val) := by
  intro u v h
  have hu : u.val < 8 ^ 6 := by norm_num; exact u.isLt
  have hv : v.val < 8 ^ 6 := by norm_num; exact v.isLt
  have hidx := congrArg index h
  rw [index_slots 6 u.val hu, index_slots 6 v.val hv] at hidx
  exact Fin.ext hidx

#print axioms length_slots
#print axioms index_slots
#print axioms foldedIndex_decompose
#print axioms slots6_injective

end AspisR1.MerkleIndexGeometry
