import PV_L2E_Dividend
set_option autoImplicit false
namespace PV_L2E_ByteWord

def value : List Nat → Nat
  | [] => 0
  | b::bs => b+256*value bs

def packed : List Nat → Nat
  | [] => 0
  | b::bs => (packed bs <<< 8) ||| b

theorem bound (bs : List Nat) (small : ∀ b∈bs,b<256) :
    value bs<256^bs.length := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
    have hb := small b (by simp)
    have ht := ih (fun x hx => small x (by simp [hx]))
    simp only [value,List.length_cons,pow_succ]
    nlinarith

/-- Shift/OR source decoding equals the positional value for arbitrary byte
length. Each OR has a disjoint low byte, without enumerating any block. -/
theorem packed_value (bs : List Nat) (small : ∀ b∈bs,b<256) :
    packed bs=value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [packed,ih (fun x hx => small x (by simp [hx])),
      ←Nat.shiftLeft_add_eq_or_of_lt (show b<2^8 from small b (by simp))]
    simp [value,Nat.shiftLeft_eq,Nat.mul_comm,Nat.add_comm]

theorem word32 (bs : List Nat) (width : bs.length=4)
    (small : ∀ b∈bs,b<256) : packed bs<2^32 ∧ packed bs % 2^32=packed bs := by
  rw [packed_value bs small]
  have h := bound bs small
  rw [width] at h
  have h' : value bs<2^32 := by simpa using h
  exact ⟨h',Nat.mod_eq_of_lt h'⟩

#print axioms bound
#print axioms packed_value
#print axioms word32
end PV_L2E_ByteWord
