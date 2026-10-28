import PV_B3P_MaskScan132
import PV_B3P_MaskModel132
namespace PV_B3P_MaskCount132
open PV_B3P_MaskScan132
set_option autoImplicit false

def pick (r c : Nat) : Bool := decide (PV_B3P_MaskModel132.free r c)
def number (p : Nat → Nat → Bool) (c r : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (if p r c then 1 else 0) + number p c (r+1) n

theorem length_rows (p : Nat → Nat → Bool) (c r n : Nat) :
    (rows p c r n).length = number p c r n := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp only [rows,number,List.length_append,ih]; split <;> simp

theorem number_add (p : Nat → Nat → Bool) (c r m n : Nat) :
    number p c r (m+n) = number p c r m + number p c (r+m) n := by
  induction m generalizing r with
  | zero => simp [number]
  | succ m ih =>
    rw [Nat.succ_add,number,number,ih]
    congr 1 <;> omega

theorem blocks (p : Nat → Nat → Bool) (c start n k : Nat)
    (h : ∀ b, b < n → number p c (start+16*b) 16 = k) :
    number p c start (16*n) = n*k := by
  induction n with
  | zero => simp [number]
  | succ n ih =>
    rw [Nat.mul_succ,number_add,ih (fun b hb => h b (by omega)),h n (by omega)]
    omega

theorem padding_block (c b : Nat) (hb : b < 57) : number pick c (16*b) 16 = 3 := by
  simp (disch := omega) [number,pick,PV_B3P_MaskModel132.free,Nat.add_mod,Nat.mul_mod]

#print axioms length_rows
#print axioms number_add
#print axioms blocks
#print axioms padding_block
end PV_B3P_MaskCount132
