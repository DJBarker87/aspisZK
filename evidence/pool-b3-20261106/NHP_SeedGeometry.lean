import Aeneas
set_option autoImplicit false
namespace NHP_SeedGeometry

theorem read_index (chunk byte : Nat) (hc : chunk < 4) (hb : byte < 7) :
    7 * chunk + byte < 28 := by omega
#print axioms read_index

theorem write_index (chunk group : Nat) (hc : chunk < 4) (hg : group < 8) :
    8 * chunk + group < 32 := by omega
#print axioms write_index

theorem discarded_tail (chunk byte index : Nat) (hc : chunk < 4) (hb : byte < 7)
    (hi : 28 ≤ index) : 7 * chunk + byte ≠ index := by omega
#print axioms discarded_tail

theorem distinct_groups (c d g h : Nat) (hg : g < 8) (hh : h < 8)
    (same : 8*c+g = 8*d+h) : c=d ∧ g=h := by omega
#print axioms distinct_groups

theorem extend_bound (word byte count : Nat) (hw : word < 256^count) (hb : byte < 256) :
    word*256+byte < 256^(count+1) := by
  have hstep : word*256+byte < (word+1)*256 := by omega
  have hmul : (word+1)*256 ≤ 256^count*256 :=
    Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt hw)
  simpa only [Nat.pow_succ] using lt_of_lt_of_le hstep hmul
#print axioms extend_bound

theorem word_limit : 256^8 = 2^64 := by
  calc
    256^8 = (2^8)^8 := congrArg (fun x : Nat => x^8) (by decide)
    _ = 2^(8*8) := (Nat.pow_mul 2 8 8).symm
    _ = 2^64 := rfl
#print axioms word_limit

theorem no_wrap (word byte : Nat) (hw : word < 256^7) (hb : byte < 256) :
    (word*256+byte) % 2^64 = word*256+byte := by
  apply Nat.mod_eq_of_lt
  rw [← word_limit]
  exact extend_bound word byte 7 hw hb
#print axioms no_wrap

theorem seven_bit (word group : Nat) :
    (word / 2^(7*(7-group))) % 128 < 128 := Nat.mod_lt _ (by decide)
#print axioms seven_bit
end NHP_SeedGeometry
