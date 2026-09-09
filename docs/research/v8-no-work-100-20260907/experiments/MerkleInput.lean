import Mathlib.Tactic
import Mathlib.Data.List.OfFn

namespace AspisV8.MerkleInput
abbrev Byte := Fin 256

-- The concrete parent buffer: one domain byte, then two 26-byte ranges.
def buffer (tag : Byte) (left right : Fin 26 → Byte) : Fin 53 → Byte :=
  Fin.append (fun _ : Fin 1 => tag) (Fin.append left right)
def slices (tag : Byte) (left right : Fin 26 → Byte) : List (List Byte) :=
  [[tag],List.ofFn left,List.ofFn right]

theorem same_parent_bytes (tag : Byte) (left right : Fin 26 → Byte) :
    List.ofFn (buffer tag left right) = (slices tag left right).flatten := by
  unfold buffer
  rw [List.ofFn_fin_append,List.ofFn_fin_append]
  have ht : List.ofFn (fun _ : Fin 1 => tag) = [tag] := rfl
  simp only [ht,slices,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]

theorem parent_length (tag : Byte) (left right : Fin 26 → Byte) :
    (slices tag left right).flatten.length = 53 := by
  rw [←same_parent_bytes]
  exact List.length_ofFn

-- Hashing is a function of the concatenated byte string. This is not a claim
-- for arbitrary Rust HashFn values, which could observe the number of slices.
theorem parent_digest_eq {Digest : Type*} (hash : List Byte → Digest)
    (tag : Byte) (left right : Fin 26 → Byte) :
    hash (List.ofFn (buffer tag left right)) = hash (slices tag left right).flatten := by
  rw [same_parent_bytes]

-- Pinned runtime4.2.1: base85; each slice costs max(10,len/2).
def syscallCost (lengths : List Nat) : Nat :=
  85 + (lengths.map (fun n => max 10 (n/2))).sum
theorem slice_cost_delta : syscallCost [1,26,26] = syscallCost [53]+10 := by
  norm_num [syscallCost]

#print axioms same_parent_bytes
#print axioms parent_length
#print axioms parent_digest_eq
#print axioms slice_cost_delta
end AspisV8.MerkleInput
