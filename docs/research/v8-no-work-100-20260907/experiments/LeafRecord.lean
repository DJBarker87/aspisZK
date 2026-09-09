import Mathlib.Tactic
import Mathlib.Data.List.TakeDrop

namespace AspisV8.LeafRecord
abbrev Byte := Fin 256

-- Literal query-record offsets, not an assumed value||salt input.
theorem c2_partition (r : List Byte) (hr : r.length = 621) :
    (r.drop 403).take 186 ++ (r.drop 589).take 32 = (r.drop 403).take 218 := by
  have hs : (r.drop 589).take 32 = r.drop 589 := by
    apply List.take_of_length_le
    simp only [List.length_drop,hr]
    omega
  have hv : (r.drop 403).take 218 = r.drop 403 := by
    apply List.take_of_length_le
    simp only [List.length_drop,hr]
    omega
  rw [hs,hv]
  exact List.drop_take_append_drop r 403 186

theorem c2_hash_eq {D : Type*} (h : List Byte → D) (tag : Byte)
    (r : List Byte) (hr : r.length = 621) :
    h ([16,tag] ++ ((r.drop 403).take 186 ++ (r.drop 589).take 32)) =
      h ([16,tag] ++ (r.drop 403).take 218) := by
  rw [c2_partition r hr]

theorem c2_preimage_length (tag : Byte) (r : List Byte) (hr : r.length = 621) :
    ([16,tag] ++ (r.drop 403).take 218).length = 220 := by
  simp only [List.length_append,List.length_cons,List.length_nil,
    List.length_take,List.length_drop,hr]
  norm_num

-- Fixed records are bounded before hashing, regardless of their byte values.
theorem query_record_bounds (i : Nat) (hi : i < 22) :
    i*621+621 ≤ 22*621 ∧ i*621+403+186 = i*621+589 ∧
      i*621+589+32 = (i+1)*621 := by omega

-- Pinned syscall charges are equal: this tests descriptor/instruction cost,
-- not fewer hashes or a cheaper SHA message.
def cost (lengths : List Nat) : Nat :=
  85 + (lengths.map (fun n => max 10 (n/2))).sum
theorem equal_syscall_cost : cost [2,186,32] = cost [2,218] := by norm_num [cost]

#print axioms c2_partition
#print axioms c2_hash_eq
#print axioms c2_preimage_length
#print axioms query_record_bounds
#print axioms equal_syscall_cost
end AspisV8.LeafRecord
