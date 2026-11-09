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


theorem sb_mod (x y : Nat) : sb x (y % 2147483647) = (x + 2147483646 * y) % 2147483647 := by
  unfold sb; omega

theorem mulsum (x y z w : Nat) :
    ((x % 2147483647 + y % 2147483647) * (z % 2147483647 + w % 2147483647)) % 2147483647
      = ((x + y) * (z + w)) % 2147483647 := by
  have h1 : (x % 2147483647 + y % 2147483647) % 2147483647 = (x + y) % 2147483647 := by omega
  have h2 : (z % 2147483647 + w % 2147483647) % 2147483647 = (z + w) % 2147483647 := by omega
  rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]

theorem hP1 (x y : Nat) (hx : x < 2147483647) (hy : y < 2147483647) : x * y < 4611686014132420609 := by
  have := Nat.mul_lt_mul'' hx hy
  omega

macro "collapse" : tactic => `(tactic| simp only [qmul, cmm, mulr, mm, ad, sb_mod, mulsum, Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mod_add_mod, Nat.add_mod_mod])

set_option maxHeartbeats 400000 in
theorem comp0 (a b c d e f g h : Nat) (ha : a < 2147483647) (hb : b < 2147483647) (hc : c < 2147483647) (hd : d < 2147483647)
    (he : e < 2147483647) (hf : f < 2147483647) (hg : g < 2147483647) (hh : h < 2147483647) :
    (qmul a b c d e f g h).1 = (gateQ a b c d e f g h).1 := by
  have h1 := hP1 b f hb hf
  have h2 := hP1 d h hd hh
  have h3 := hP1 c g hc hg
  have h4 := hP1 c h hc hh
  have h5 := hP1 d g hd hg
  collapse
  simp only [gateQ, clos]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

set_option maxHeartbeats 400000 in
theorem comp1 (a b c d e f g h : Nat) (ha : a < 2147483647) (hb : b < 2147483647) (hc : c < 2147483647) (hd : d < 2147483647)
    (he : e < 2147483647) (hf : f < 2147483647) (hg : g < 2147483647) (hh : h < 2147483647) :
    (qmul a b c d e f g h).2.1 = (gateQ a b c d e f g h).2.1 := by
  have h1 := hP1 b f hb hf
  have h2 := hP1 d h hd hh
  have h3 := hP1 c g hc hg
  have h4 := hP1 c h hc hh
  have h5 := hP1 d g hd hg
  collapse
  simp only [gateQ, clos]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

set_option maxHeartbeats 400000 in
theorem comp2 (a b c d e f g h : Nat) (ha : a < 2147483647) (hb : b < 2147483647) (hc : c < 2147483647) (hd : d < 2147483647)
    (he : e < 2147483647) (hf : f < 2147483647) (hg : g < 2147483647) (hh : h < 2147483647) :
    (qmul a b c d e f g h).2.2.1 = (gateQ a b c d e f g h).2.2.1 := by
  have h1 := hP1 b h hb hh
  have h2 := hP1 d f hd hf
  collapse
  simp only [gateQ, clos]
  simp only [Nat.add_mul, Nat.mul_add]
  omega

set_option maxHeartbeats 400000 in
theorem comp3 (a b c d e f g h : Nat) (ha : a < 2147483647) (hb : b < 2147483647) (hc : c < 2147483647) (hd : d < 2147483647)
    (he : e < 2147483647) (hf : f < 2147483647) (hg : g < 2147483647) (hh : h < 2147483647) :
    (qmul a b c d e f g h).2.2.2 = (gateQ a b c d e f g h).2.2.2 := by
  collapse
  simp only [gateQ, clos]
  simp only [Nat.add_mul, Nat.mul_add]
  omega
#print axioms comp0
#print axioms comp1
#print axioms comp2
#print axioms comp3
end PCVB_QM