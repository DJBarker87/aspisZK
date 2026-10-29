import R1Z.PV_OWNK_TowerCanon
set_option autoImplicit false
namespace R1Z.PV_OWNL_InputBytes
open Aeneas Aeneas.Std PV_OWNK_TowerCanon

def le4 (x : Nat) : Nat × Nat × Nat × Nat :=
 (x%256,(x/256)%256,(x/65536)%256,(x/16777216)%256)
def read4 (b : Nat × Nat × Nat × Nat) : Nat :=
 b.1 + 256*b.2.1 + 65536*b.2.2.1 + 16777216*b.2.2.2

theorem read_write (x : Nat) (hx : x < 4294967296) : read4 (le4 x) = x := by
 have h0 := Nat.mod_add_div x 256
 have h1 := Nat.mod_add_div (x/256) 256
 have h2 := Nat.mod_add_div (x/65536) 256
 have h3 := Nat.mod_add_div (x/16777216) 256
 have hd1 : x/256/256 = x/65536 := by rw [Nat.div_div_eq_div_mul]
 have hd2 : x/65536/256 = x/16777216 := by rw [Nat.div_div_eq_div_mul]
 have hd3 : x/16777216/256 = 0 := by
  rw [Nat.div_div_eq_div_mul]; exact Nat.div_eq_of_lt hx
 rw [hd1] at h1
 rw [hd2] at h2
 rw [hd3] at h3
 simp only [read4,le4,Prod.fst,Prod.snd]
 omega

def checked (q : Q) : Bool :=
 decide (read4 (le4 q.c0.a.val) < 2147483647 ∧
 read4 (le4 q.c0.b.val) < 2147483647 ∧
 read4 (le4 q.c1.a.val) < 2147483647 ∧
 read4 (le4 q.c1.b.val) < 2147483647)

theorem checked_iff (q : Q) : checked q = true ↔ Canon q := by
 simp only [checked,decide_eq_true_eq,
  read_write _ q.c0.a.hBounds,read_write _ q.c0.b.hBounds,
  read_write _ q.c1.a.hBounds,read_write _ q.c1.b.hBounds]
 exact and_assoc.symm

/-- The builder's successful all-elements check supplies g/d bounds. -/
theorem accepted_canonical (values : List Q)
 (h : values.all checked = true) : ∀ q ∈ values, Canon q := by
 intro q hq
 exact (checked_iff q).mp ((List.all_eq_true.mp h) q hq)
#print axioms read_write
#print axioms checked_iff
#print axioms accepted_canonical
end R1Z.PV_OWNL_InputBytes
