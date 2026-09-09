import Mathlib.Tactic
namespace AspisV8.QmCross
def p : Nat := 2147483647
def word : Nat := 18446744073709551616
theorem product_lt {a b : Nat} (ha:a<p) (hb:b<p) : a*b<p^2 := by
  have h:=Nat.mul_le_mul (show a≤p-1 by omega) (show b≤p-1 by omega)
  have e : (p-1)*(p-1)<p^2 := by norm_num [p]
  omega
theorem four_range {a b c d : Nat}
    (ha:a<p^2) (hb:b<p^2) (hc:c<p^2) (hd:d<p^2) :
    a+b+c+d<word := by
  have h : 4*p^2<word := by norm_num [p,word]
  omega
theorem signed_prefixes {a b c d : Nat}
    (ha:a<p^2) (hb:b<p^2) (hc:c<p^2) (hd:d<p^2) :
    a+b<word ∧ a+b+2*p^2<word ∧ c≤a+b+2*p^2 ∧
    d≤a+b+2*p^2-c ∧ a+b+2*p^2-c-d<word := by
  have h : 4*p^2<word := by norm_num [p,word]
  omega
theorem signed_mod (a b c d : Int) :
    (a+b+2*(p:Int)^2-c-d)%(p:Int)=(a+b-c-d)%(p:Int) := by
  simp [pow_two,Int.add_emod,Int.sub_emod,Int.mul_emod]
theorem cross_real {K : Type*} [CommRing K] (a b c d e f g h : K) :
    ((a+c)*(e+g)-(b+d)*(f+h))-(a*e-b*f)-(c*g-d*h)
      = a*g+c*e-b*h-d*f := by ring
theorem cross_imag {K : Type*} [CommRing K] (a b c d e f g h : K) :
    ((a+c)*(f+h)+(b+d)*(e+g))-(a*f+b*e)-(c*h+d*g)
      = a*h+b*g+c*f+d*e := by ring
#print axioms product_lt
#print axioms four_range
#print axioms signed_prefixes
#print axioms signed_mod
#print axioms cross_real
#print axioms cross_imag
def partialFold (x : Nat) := x%(p+1)+x/(p+1)
theorem partial_congr (x : Nat) : partialFold x%p=x%p := by
  have h:=Nat.mod_add_div x (p+1)
  calc
    partialFold x%p=(x%(p+1)+(p+1)*(x/(p+1)))%p := by
      dsimp [partialFold]
      rw [Nat.add_mod (x%(p+1)) (x/(p+1)) p,
        Nat.add_mod (x%(p+1)) ((p+1)*(x/(p+1))) p,
        Nat.mul_mod (p+1) (x/(p+1)) p]
      norm_num [p]
    _=x%p := by rw [h]
theorem partial_range {x n : Nat} (hx:x<n*p^2) : partialFold x<(n+1)*p := by
  have hr:=Nat.mod_lt x (by norm_num [p] : 0<p+1)
  have hd : x/(p+1)<n*p := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num [p])).2
    have : n*p^2≤n*p*(p+1) := by nlinarith
    exact lt_of_lt_of_le hx this
  dsimp [partialFold,p] at *; omega
theorem lazy_c0_prefixes {a b c d : Nat}
    (ha:a<4*p) (hb:b<4*p) (hc:c<3*p) (hd:d<2*p) :
    a+8*p<word ∧ b≤a+8*p ∧ c≤a+8*p-b ∧
    a+2*c+8*p<word ∧ d≤a+2*c+8*p := by
  dsimp [p,word] at *;omega
theorem pad8_mod (x y : Int) :
    (x+8*(p:Int)-y)%(p:Int)=(x-y)%(p:Int) := by
  simp [Int.add_emod,Int.sub_emod,Int.mul_emod]
#print axioms partial_congr
#print axioms partial_range
#print axioms lazy_c0_prefixes
#print axioms pad8_mod
theorem c0_real {K : Type*} [CommRing K] (a b c d e f g h : K) :
    (a*e-b*f)+(2*(c*g-d*h)-(c*h+d*g))
      = (a*e+2*(c*g))-(b*f+2*(d*h))-(c*h+d*g) := by ring
theorem c0_imag {K : Type*} [CommRing K] (a b c d e f g h : K) :
    (a*f+b*e)+((c*g-d*h)+2*(c*h+d*g))
      = (a*f+b*e+c*g)+2*(c*h+d*g)-d*h := by ring
#print axioms c0_real
#print axioms c0_imag
theorem partial_list (xs : List Nat) :
    (xs.map partialFold).sum%p=xs.sum%p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [Nat.add_mod (partialFold a) _,Nat.add_mod a _,partial_congr,ih]
theorem seven_partial_range (x : Fin 7 → Nat) (hx : ∀ i, x i<4*p^2) :
    (∑ i, partialFold (x i))<2^37 := by
  have h : (∑ i, partialFold (x i))≤∑ _i : Fin 7, 5*p :=
    Finset.sum_le_sum fun i _ => Nat.le_of_lt (partial_range (hx i))
  have e : (∑ _i : Fin 7, 5*p)<2^37 := by norm_num [p]
  omega
#print axioms partial_list
#print axioms seven_partial_range

theorem raw_partial_range (x : Nat) (hx : x < word) : partialFold x < 5*p+4 := by
  have hr := Nat.mod_lt x (by norm_num [p] : 0<p+1)
  have hd : x/(p+1) < 8589934592 := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num [p])).2
    norm_num [p, word] at *
    exact hx
  dsimp [partialFold,p] at *; omega

theorem channel_reconstruction {K : Type*} [CommRing K]
    (a b c d e f g h i : K) :
    ((a-b)+2*(d-e)-(f-d-e),
      (c-a-b)+(d-e)+2*(f-d-e),
      (g-h)-(a-b)-(d-e),
      (i-g-h)-(c-a-b)-(f-d-e)) =
    (a+3*d-b-e-f, c+2*f-a-b-d-3*e,
      g+b+e-h-a-d, i+a+b+d+e-g-h-c-f) := by
  apply Prod.ext
  · ring
  apply Prod.ext
  · ring
  apply Prod.ext <;> ring

theorem channel_prefix_ranges (a b c d e f g h i : Nat)
    (ha:a<5*p+4) (hb:b<5*p+4) (hc:c<5*p+4) (hd:d<5*p+4) (he:e<5*p+4)
    (hf:f<5*p+4) (hg:g<5*p+4) (hh:h<5*p+4) (hi:i<5*p+4) :
    a+3*d+32*p < word ∧ b+e+f ≤ a+3*d+32*p ∧
    c+2*f+32*p < word ∧ a+b+d+3*e ≤ c+2*f+32*p ∧
    g+b+e+32*p < word ∧ h+a+d ≤ g+b+e+32*p ∧
    i+a+b+d+e+32*p < word ∧ g+h+c+f ≤ i+a+b+d+e+32*p := by
  dsimp [p,word] at *; omega

theorem pad32_mod (x : Int) :
    (x+32*(p:Int))%(p:Int)=x%(p:Int) := by
  simp [Int.add_emod,Int.mul_emod]

def channelMod (s : Fin 9 → Int) : Int × Int × Int × Int :=
  ((s 0+3*s 3-s 1-s 4-s 5)%(p:Int),
    (s 2+2*s 5-s 0-s 1-s 3-3*s 4)%(p:Int),
    (s 6+s 1+s 4-s 7-s 0-s 3)%(p:Int),
    (s 8+s 0+s 1+s 3+s 4-s 6-s 7-s 2-s 5)%(p:Int))

theorem channel_mod_congr (s t : Fin 9 → Int)
    (h : ∀ i, s i%(p:Int)=t i%(p:Int)) : channelMod s=channelMod t := by
  have hh : ∀ i, Int.ModEq (p:Int) (s i) (t i) := h
  unfold channelMod
  apply Prod.ext
  · exact ((((hh 0).add ((hh 3).mul_left 3)).sub (hh 1)).sub (hh 4)).sub (hh 5)
  apply Prod.ext
  · exact (((((hh 2).add ((hh 5).mul_left 2)).sub (hh 0)).sub (hh 1)).sub (hh 3)).sub ((hh 4).mul_left 3)
  apply Prod.ext
  · exact (((((hh 6).add (hh 1)).add (hh 4)).sub (hh 7)).sub (hh 0)).sub (hh 3)
  · exact ((((((((hh 8).add (hh 0)).add (hh 1)).add (hh 3)).add (hh 4)).sub (hh 6)).sub (hh 7)).sub (hh 2)).sub (hh 5)

theorem raw_channel_partial_congr (s : Fin 9 → Nat) :
    channelMod (fun i => (partialFold (s i):Int)) =
    channelMod (fun i => (s i:Int)) := by
  apply channel_mod_congr
  intro i
  exact_mod_cast partial_congr (s i)

#print axioms raw_partial_range
#print axioms channel_reconstruction
#print axioms channel_prefix_ranges
#print axioms pad32_mod
#print axioms channel_mod_congr
#print axioms raw_channel_partial_congr

theorem two_partial_range (x y : Nat) (hx:x<word) (hy:y<word) :
    partialFold x+partialFold y < word := by
  have hx' := raw_partial_range x hx
  have hy' := raw_partial_range y hy
  dsimp [p,word] at *;omega

theorem two_partial_congr (x y : Nat) :
    (partialFold x+partialFold y)%p=(x+y)%p := by
  rw [Nat.add_mod, partial_congr, partial_congr, ← Nat.add_mod]

#print axioms two_partial_range
#print axioms two_partial_congr
end AspisV8.QmCross
