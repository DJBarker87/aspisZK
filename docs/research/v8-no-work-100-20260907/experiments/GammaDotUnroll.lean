import Mathlib.Tactic

namespace AspisV8.GammaDotUnroll

def p : Nat := 2147483647
def word : Nat := 2^64

def loop (c : Fin 7 → Nat) : Nat :=
  ((((((0+c 0)+c 1)+c 2)+c 3)+c 4)+c 5)+c 6
def fixed (c : Fin 7 → Nat) : Nat :=
  ((c 0+c 1)+(c 2+c 3))+((c 4+c 5)+c 6)

-- The reducer can be arbitrary: its application boundaries are unchanged.
theorem fixed_eq_loop (reduce : Nat → Nat) (raw : Fin 7 → Nat) :
    fixed (reduce ∘ raw) = loop (reduce ∘ raw) := by
  simp only [fixed,loop]
  omega

theorem fixed_bound (c : Fin 7 → Nat) (hc : ∀ i, c i < 5*p) :
    fixed c < 35*p := by
  have h0:=hc 0; have h1:=hc 1; have h2:=hc 2; have h3:=hc 3
  have h4:=hc 4; have h5:=hc 5; have h6:=hc 6
  simp only [fixed]
  omega

def wrapped (c : Fin 7 → Nat) : Nat :=
  (((((c 0+c 1)%word)+((c 2+c 3)%word))%word)
    +(((((c 4+c 5)%word)+c 6)%word)))%word

theorem wrapped_eq_fixed (c : Fin 7 → Nat) (hc : ∀ i, c i < 5*p) :
    wrapped c = fixed c := by
  have h0:=hc 0; have h1:=hc 1; have h2:=hc 2; have h3:=hc 3
  have h4:=hc 4; have h5:=hc 5; have h6:=hc 6
  norm_num [p] at h0 h1 h2 h3 h4 h5 h6
  have h01 : c 0+c 1<word := by norm_num [word]; omega
  have h23 : c 2+c 3<word := by norm_num [word]; omega
  have h45 : c 4+c 5<word := by norm_num [word]; omega
  have h03 : (c 0+c 1)+(c 2+c 3)<word := by norm_num [word]; omega
  have h46 : (c 4+c 5)+c 6<word := by norm_num [word]; omega
  have hall : ((c 0+c 1)+(c 2+c 3))+((c 4+c 5)+c 6)<word := by
    norm_num [word]; omega
  simp only [wrapped,Nat.mod_eq_of_lt h01,Nat.mod_eq_of_lt h23,
    Nat.mod_eq_of_lt h45,Nat.mod_eq_of_lt h03,Nat.mod_eq_of_lt h46,
    Nat.mod_eq_of_lt hall,fixed]

-- Applies to canonical reduction (<p) and the selected one-fold partial
-- reduction (<5p). The four-product dot / mask-shift reduction facts remain
-- the unchanged M31RangeKernels and QmCrossRange obligations.
theorem selected_endpoint (reduce : Nat → Nat) (raw : Fin 7 → Nat)
    (hc : ∀ i, reduce (raw i) < 5*p) :
    wrapped (reduce ∘ raw) = loop (reduce ∘ raw) := by
  exact (wrapped_eq_fixed (reduce ∘ raw) hc).trans (fixed_eq_loop reduce raw)

#print axioms fixed_eq_loop
#print axioms fixed_bound
#print axioms wrapped_eq_fixed
#print axioms selected_endpoint
end AspisV8.GammaDotUnroll
