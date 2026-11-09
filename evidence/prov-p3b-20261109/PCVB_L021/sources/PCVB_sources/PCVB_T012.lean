set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace PCVB_QM

abbrev PP : Nat := 2147483647
def mm (x y : Nat) : Nat := x * y % 2147483647
def sb (x y : Nat) : Nat := (x + 2147483647 - y) % 2147483647
def ad (x y : Nat) : Nat := (x + y) % 2147483647
def clos (x : Nat) : Nat := x % 2147483648 + x / 2147483648

/-- frozen CM31.mul on limbs (x,y)*(z,w); result (re, im) -/
def cmm (x y z w : Nat) : Nat × Nat :=
  (sb (mm x z) (mm y w), sb (sb (((x + y) * (z + w)) % 2147483647) (mm x z)) (mm y w))

def mulr (p q : Nat) : Nat × Nat := (sb (ad p p) q, ad p (ad q q))

def qmul (a b c d e f g h : Nat) : Nat × Nat × Nat × Nat :=
  let m0 := cmm a b e f
  let m1 := cmm c d g h
  let s := (ad a c, ad b d)
  let s1 := (ad e g, ad f h)
  let m2 := cmm s.1 s.2 s1.1 s1.2
  let c2 := mulr m1.1 m1.2
  let c3 := (ad m0.1 c2.1, ad m0.2 c2.2)
  let c4 := (sb m2.1 m0.1, sb m2.2 m0.2)
  let c5 := (sb c4.1 m1.1, sb c4.2 m1.2)
  (c3.1, c3.2, c5.1, c5.2)

def gateQ (a b c d e f g h : Nat) : Nat × Nat × Nat × Nat :=
  let u := clos (c * g + 4611686014132420609 - d * h)
  let v := clos (c * h + d * g)
  ((a * e + 4611686014132420609 - b * f + 2 * u + 3 * 2147483647 - v) % 2147483647,
   (a * f + b * e + u + 2 * v) % 2147483647,
   (a * g + c * e + 2 * 4611686014132420609 - b * h - d * f) % 2147483647,
   (a * h + b * g + c * f + d * e) % 2147483647)


theorem sb_mod (x y : Nat) : sb x (y % 2147483647) = (x + 2146483646 * y) % 2147483647 := by
  unfold sb; omega

theorem mulsum (x y z w : Nat) :
    ((x % 2147483647 + y % 2147483647) * (z % 2147483647 + w % 2147483647)) % 2147483647
      = ((x + y) * (z + w)) % 2147483647 := by
  have h1 : (x % 2147483647 + y % 2147483647) % 2147483647 = (x + y) % 2147483647 := by omega
  have h2 : (z % 2147483647 + w % 2147483647) % 2147483647 = (z + w) % 2147483647 := by omega
  rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]

set_option maxHeartbeats 400000 in
theorem comp0_collapse (a b c d e f g h : Nat) :
    (qmul a b c d e f g h).1 = 0 := by
  simp only [qmul, cmm, mulr, mm, ad, sb_mod, mulsum, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mod_add_mod, Nat.add_mod_mod, Nat.mod_mod]
  trace_state
  sorry
end PCVB_QM