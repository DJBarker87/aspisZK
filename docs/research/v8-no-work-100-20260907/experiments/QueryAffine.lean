import SharedGammaDots
namespace AspisV8.QueryAffine
open AspisV8.AffinePrimal AspisV8.SemanticCarry AspisV8.SharedGammaDots
open scoped BigOperators
def cap : Nat := 7*(5*p+3)
def balanced (c : Fin 7 → Nat) : Nat :=
  ((c 0+c 1)+(c 2+c 3))+((c 4+c 5)+c 6)
def rawLimb (r : Fin 7 → Nat) := balanced (fun i => part (r i))
theorem raw_limb_bound (r : Fin 7 → Nat) (hr:∀ i,r i<word) : rawLimb r≤cap := by
  have hf (i:Fin 7) : part (r i)≤5*p+3 := by
    have h:=AspisV8.QmCross.raw_partial_range (r i) (hr i)
    change part (r i)<5*p+4 at h
    omega
  have h0:=hf 0;have h1:=hf 1;have h2:=hf 2;have h3:=hf 3
  have h4:=hf 4;have h5:=hf 5;have h6:=hf 6
  dsimp [rawLimb,balanced,cap]
  omega
theorem balanced_wraps_exact (c : Fin 7 → Nat) (hc:∀ i,c i≤5*p+3) :
    (((c 0+c 1)%word+(c 2+c 3)%word)%word+
      (((c 4+c 5)%word+c 6)%word))%word=balanced c := by
  have h0:=hc 0;have h1:=hc 1;have h2:=hc 2;have h3:=hc 3
  have h4:=hc 4;have h5:=hc 5;have h6:=hc 6
  have h01:c 0+c 1<word := by dsimp [p,word] at *;omega
  have h23:c 2+c 3<word := by dsimp [p,word] at *;omega
  have h45:c 4+c 5<word := by dsimp [p,word] at *;omega
  have h03:(c 0+c 1)+(c 2+c 3)<word := by dsimp [p,word] at *;omega
  have h46:(c 4+c 5)+c 6<word := by dsimp [p,word] at *;omega
  have htotal:balanced c<word := by dsimp [balanced,p,word] at *;omega
  simp only [Nat.mod_eq_of_lt h01,Nat.mod_eq_of_lt h23,Nat.mod_eq_of_lt h45,
    Nat.mod_eq_of_lt h03,Nat.mod_eq_of_lt h46]
  exact Nat.mod_eq_of_lt htotal

-- Exact six four-product groups and final pair, with the source's indices.
def chunks (f : Nat → Nat) : Fin 7 → Nat :=
  ![f 0+f 1+f 2+f 3,f 4+f 5+f 6+f 7,f 8+f 9+f 10+f 11,
    f 12+f 13+f 14+f 15,f 16+f 17+f 18+f 19,
    f 20+f 21+f 22+f 23,f 24+f 25]
theorem chunk_bound (f : Nat → Nat) (hf:∀ i,i<26 → f i≤m^2) (j:Fin 7) :
    chunks f j<word := by
  have h0:=hf 0 (by omega)
  have h1:=hf 1 (by omega)
  have h2:=hf 2 (by omega)
  have h3:=hf 3 (by omega)
  have h4:=hf 4 (by omega)
  have h5:=hf 5 (by omega)
  have h6:=hf 6 (by omega)
  have h7:=hf 7 (by omega)
  have h8:=hf 8 (by omega)
  have h9:=hf 9 (by omega)
  have h10:=hf 10 (by omega)
  have h11:=hf 11 (by omega)
  have h12:=hf 12 (by omega)
  have h13:=hf 13 (by omega)
  have h14:=hf 14 (by omega)
  have h15:=hf 15 (by omega)
  have h16:=hf 16 (by omega)
  have h17:=hf 17 (by omega)
  have h18:=hf 18 (by omega)
  have h19:=hf 19 (by omega)
  have h20:=hf 20 (by omega)
  have h21:=hf 21 (by omega)
  have h22:=hf 22 (by omega)
  have h23:=hf 23 (by omega)
  have h24:=hf 24 (by omega)
  have h25:=hf 25 (by omega)
  have hcap:4*m^2<word := by norm_num [m,p,word]
  fin_cases j <;> simp [chunks] <;> omega
theorem actual_c1_sum (f : Nat → Nat) :
    (rawLimb (chunks f):ZMod p)=∑ i∈Finset.range 26,(f i:ZMod p) := by
  simp [rawLimb,balanced,partial_cast,chunks,Finset.sum_range_succ]
  ring

theorem offsets_bound_wide {a b c d:Nat} (ha:a≤cap) (hb:b≤cap) (hc:c≤cap) (hd:d≤cap) :
    a≤4*cap ∧ a+b≤4*cap ∧ a+c≤4*cap ∧ b+d≤4*cap ∧ (a+c)+(b+d)≤4*cap := by omega
theorem raw_channel_bound_wide {s c:Nat} (hs:s≤3*m^2) (hc:c≤4*cap) : s+c<word := by
  have h:3*m^2+4*cap<word := by norm_num [cap,m,p,word]
  omega
theorem raw_channel_exact_wide {s c:Nat} (hs:s≤3*m^2) (hc:c≤4*cap) :
    wrap s c=s+c := Nat.mod_eq_of_lt (raw_channel_bound_wide hs hc)
theorem offset_adds_exact_wide {a b c d:Nat} (ha:a≤cap) (hb:b≤cap) (hc:c≤cap) (hd:d≤cap) :
    wrap a b=a+b ∧ wrap a c=a+c ∧ wrap b d=b+d ∧
      wrap (wrap a c) (wrap b d)=(a+c)+(b+d) := by
  have h:4*cap<word := by norm_num [cap,p,word]
  have hab:a+b<word := by omega
  have hac:a+c<word := by omega
  have hbd:b+d<word := by omega
  have hall:(a+c)+(b+d)<word := by omega
  simp only [wrap,Nat.mod_eq_of_lt hab,Nat.mod_eq_of_lt hac,
    Nat.mod_eq_of_lt hbd,Nat.mod_eq_of_lt hall,and_self]
theorem helper_prefix (n s a b:Nat) (hn:n<3) (hs:s≤n*m^2) (ha:a≤m) (hb:b≤m) :
    s+a*b≤(n+1)*m^2 ∧ (s+(a*b)%word)%word=s+a*b :=
  four_product_prefix n s a b (by omega) hs ha hb
theorem seeded_helper_prefix (n s a b:Nat) (hn:n<3) (hs:s≤n*m^2+4*cap)
    (ha:a≤m) (hb:b≤m) :
    s+a*b≤(n+1)*m^2+4*cap ∧ (s+(a*b)%word)%word=s+a*b := by
  have hab:a*b≤m^2 := by simpa [pow_two] using Nat.mul_le_mul ha hb
  have hpost:s+a*b≤(n+1)*m^2+4*cap := by nlinarith
  have hcap:(n+1)*m^2+4*cap≤3*m^2+4*cap :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
  have hceil:3*m^2+4*cap<word := by norm_num [m,p,cap,word]
  have hw:s+a*b<word := lt_of_le_of_lt (hpost.trans hcap) hceil
  exact ⟨hpost,by rw [Nat.mod_eq_of_lt (show a*b<word by omega),Nat.mod_eq_of_lt hw]⟩

-- Alternative lowering: install the same constant before the three updates.
-- This controls the C1 seed's live range; it is not a different field formula.
theorem seeded_channels_equal (xs:List (Q Nat × Q Nat)) (v:Q Nat) :
    xs.foldl (fun s xy => s+productsN xy.1 xy.2) (inject 0 (v 0) (v 1) (v 2) (v 3))=
      inject (rawGroup xs) (v 0) (v 1) (v 2) (v 3) := by
  rw [fold_seed]
  change inject 0 (v 0) (v 1) (v 2) (v 3)+rawGroup xs=_
  funext i j
  fin_cases i <;> fin_cases j <;> simp [inject] <;> omega

def fused (xs:List (Q Nat × Q Nat)) (v:Q Nat) : Q (ZMod p) :=
  reconstruct (castC (inject (rawGroup xs) (v 0) (v 1) (v 2) (v 3)))
theorem helper_result (xs:List (Q Nat × Q Nat)) :
    reconstruct (castC (rawGroup xs))=
      xs.foldl (fun t xy => t+towerMul (castQ xy.1) (castQ xy.2)) 0 := by
  have hz:castC (0:C Nat)=(0:C (ZMod p)) := by funext i j;simp [castC]
  rw [rawGroup,cast_raw_fold,hz]
  have h:=accumulate_reconstructs
    (xs.map (fun xy => (castQ xy.1,castQ xy.2))) (0:C (ZMod p))
  have hr0:reconstruct (0:C (ZMod p))=(0:Q (ZMod p)) := by
    funext i;fin_cases i <;> simp [reconstruct]
  simpa only [List.foldl_map,hr0] using h
theorem raw_affine_result (xs:List (Q Nat × Q Nat)) (v:Q Nat) :
    fused xs v=
      xs.foldl (fun t xy => t+towerMul (castQ xy.1) (castQ xy.2)) (castQ v) := by
  have hv:![(v 0:ZMod p),(v 1:ZMod p),(v 2:ZMod p),(v 3:ZMod p)]=castQ v := by
    funext i;fin_cases i <;> rfl
  change reconstruct (fun i j =>
    ((inject (rawGroup xs) (v 0) (v 1) (v 2) (v 3) i j:Nat):ZMod p))=_
  rw [raw_injection_reconstructs,hv]
  change reconstruct (castC (rawGroup xs))+castQ v=_
  rw [helper_result,fold_seed
    (fun xy:Q Nat × Q Nat => towerMul (castQ xy.1) (castQ xy.2)) xs (castQ v)]
  exact add_comm _ _
theorem canonical_constant_equivalent (xs:List (Q Nat × Q Nat)) (v:Q Nat) :
    fused xs v=fused xs (fun i => v i%p) := by
  rw [raw_affine_result,raw_affine_result]
  congr 1
  funext i
  simp [castQ]
theorem byte_neutral_inventory : 22*4=88 ∧ 88*4=352 ∧
    697*16+52+24+22*621+2*296*26=40282 := by norm_num
#print axioms raw_limb_bound
#print axioms balanced_wraps_exact
#print axioms chunk_bound
#print axioms actual_c1_sum
#print axioms offsets_bound_wide
#print axioms raw_channel_bound_wide
#print axioms raw_channel_exact_wide
#print axioms offset_adds_exact_wide
#print axioms helper_prefix
#print axioms seeded_helper_prefix
#print axioms seeded_channels_equal
#print axioms helper_result
#print axioms raw_affine_result
#print axioms canonical_constant_equivalent
#print axioms byte_neutral_inventory
end AspisV8.QueryAffine
