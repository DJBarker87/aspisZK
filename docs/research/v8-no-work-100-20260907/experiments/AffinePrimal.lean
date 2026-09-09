import Mathlib.Tactic
namespace AspisV8.AffinePrimal
variable {R : Type*} [CommRing R]
def reconstruct (s : Fin 3 → Fin 3 → R) : Fin 4 → R :=
  let ar := s 0 0-s 0 1
  let ai := s 0 2-s 0 0-s 0 1
  let br := s 1 0-s 1 1
  let bi := s 1 2-s 1 0-s 1 1
  let cr := s 2 0-s 2 1
  let ci := s 2 2-s 2 0-s 2 1
  ![ar+(2*br-bi),ai+(br+2*bi),cr-ar-br,ci-ai-bi]
def inject {S : Type*} [Add S] (s : Fin 3 → Fin 3 → S) (a b c d : S) :
    Fin 3 → Fin 3 → S :=
  ![![s 0 0+a,s 0 1,s 0 2+(a+b)],
    ![s 1 0,s 1 1,s 1 2],
    ![s 2 0+(a+c),s 2 1,s 2 2+((a+c)+(b+d))]]

-- Literal nine-channel reconstruction and four updates of the source kernel.
theorem injected_constant (s : Fin 3 → Fin 3 → R) (a b c d : R) :
    reconstruct (inject s a b c d)=reconstruct s+![a,b,c,d] := by
  funext i
  fin_cases i <;> simp [reconstruct,inject] <;> ring

theorem inject_cast (s : Fin 3 → Fin 3 → Nat) (a b c d : Nat) :
    (fun i j => ((inject s a b c d i j : Nat) : R)) =
      inject (fun i j => (s i j : R)) (a:R) (b:R) (c:R) (d:R) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [inject]

theorem raw_injection_reconstructs (s : Fin 3 → Fin 3 → Nat) (a b c d : Nat) :
    reconstruct (fun i j => ((inject s a b c d i j : Nat) : R)) =
      reconstruct (fun i j => (s i j : R))+![(a:R),(b:R),(c:R),(d:R)] := by
  rw [inject_cast, injected_constant]

def p : Nat := 2147483647
def m : Nat := p-1
def word : Nat := 18446744073709551616
def wrap (a b : Nat) := (a+b)%word
theorem offsets_bound {a b c d : Nat}
    (ha:a≤m) (hb:b≤m) (hc:c≤m) (hd:d≤m) :
    a≤4*m ∧ a+b≤4*m ∧ a+c≤4*m ∧ b+d≤4*m ∧ (a+c)+(b+d)≤4*m := by omega
theorem raw_channel_bound {s c : Nat} (hs:s≤3*m^2) (hc:c≤4*m) : s+c<word := by
  have h : 3*m^2+4*m<word := by norm_num [m,p,word]
  omega
theorem raw_channel_exact {s c : Nat} (hs:s≤3*m^2) (hc:c≤4*m) : wrap s c=s+c :=
  Nat.mod_eq_of_lt (raw_channel_bound hs hc)
theorem offset_adds_exact {a b c d : Nat}
    (ha:a≤m) (hb:b≤m) (hc:c≤m) (hd:d≤m) :
    wrap a b=a+b ∧ wrap a c=a+c ∧ wrap b d=b+d ∧
      wrap (wrap a c) (wrap b d)=(a+c)+(b+d) := by
  have hm : 4*m<word := by norm_num [m,p,word]
  have hab:a+b<word := by omega
  have hac:a+c<word := by omega
  have hbd:b+d<word := by omega
  have hsum:(a+c)+(b+d)<word := by omega
  simp only [wrap, Nat.mod_eq_of_lt hab,Nat.mod_eq_of_lt hac,
    Nat.mod_eq_of_lt hbd,Nat.mod_eq_of_lt hsum,and_self]

-- Each unchanged channel is a sum of three products of canonical field limbs.
theorem three_products_bound {a b c d e f : Nat}
    (ha:a≤m) (hb:b≤m) (hc:c≤m) (hd:d≤m) (he:e≤m) (hf:f≤m) :
    a*b+c*d+e*f≤3*m^2 := by
  have h0 : a*b≤m^2 := by simpa [pow_two] using Nat.mul_le_mul ha hb
  have h1 : c*d≤m^2 := by simpa [pow_two] using Nat.mul_le_mul hc hd
  have h2 : e*f≤m^2 := by simpa [pow_two] using Nat.mul_le_mul he hf
  omega

theorem three_pass_inventory : 256/4=64 ∧ 64/4=16 ∧ 16/4=4 ∧
    64+16+4=84 ∧ 4*84=336 := by norm_num
#print axioms injected_constant
#print axioms inject_cast
#print axioms raw_injection_reconstructs
#print axioms offsets_bound
#print axioms raw_channel_bound
#print axioms raw_channel_exact
#print axioms offset_adds_exact
#print axioms three_products_bound
#print axioms three_pass_inventory
end AspisV8.AffinePrimal
