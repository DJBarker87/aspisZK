import Mathlib.Tactic
namespace AspisV8.M31Range
def p : Nat := 2147483647
def w32 : Nat := 4294967296
def w64 : Nat := 18446744073709551616
def wrapAdd (w a b : Nat) := (a+b)%w
def wrapSub (w a b : Nat) := (a+w-b)%w
def subP (s : Nat) := if p ≤ s then s-p else s
def fastSubP (s : Nat) := if p ≤ s then wrapSub w32 s p else s

theorem wrap_add_exact {w a b : Nat} (h : a+b<w) :
    wrapAdd w a b = a+b := Nat.mod_eq_of_lt h
theorem wrap_sub_exact {w a b : Nat} (h : b≤a) (ha : a<w) :
    wrapSub w a b = a-b := by
  unfold wrapSub
  rw [show a+w-b=(a-b)+w by omega, Nat.add_mod]
  simp [Nat.mod_eq_of_lt (show a-b<w by omega)]

theorem add_word_bound {a b : Nat} (ha : a<p) (hb : b<p) : a+b<w32 := by
  dsimp [p,w32] at *; omega
theorem sub_word_bounds {a b : Nat} (ha : a<p) (hb : b<p) :
    a+p<w32 ∧ b≤a+p ∧ a+p-b<w32 := by
  dsimp [p,w32] at *; omega
theorem conditional_sub_exact {s : Nat} (hs : s<w32) : fastSubP s=subP s := by
  unfold fastSubP subP
  split_ifs with h
  · exact wrap_sub_exact h hs
  · rfl

theorem add_kernel_exact {a b : Nat} (ha : a<p) (hb : b<p) :
    fastSubP (wrapAdd w32 a b)=subP (a+b) := by
  rw [wrap_add_exact (add_word_bound ha hb)]
  exact conditional_sub_exact (add_word_bound ha hb)
theorem sub_kernel_exact {a b : Nat} (ha : a<p) (hb : b<p) :
    fastSubP (wrapSub w32 (wrapAdd w32 a p) b)=subP (a+p-b) := by
  obtain ⟨h0,h1,h2⟩:=sub_word_bounds ha hb
  rw [wrap_add_exact h0, wrap_sub_exact h1 h0]
  exact conditional_sub_exact h2
theorem neg_kernel_exact {a : Nat} (ha : a<p) :
    (if a=0 then 0 else wrapSub w32 p a)=(if a=0 then 0 else p-a) := by
  split_ifs
  · rfl
  · exact wrap_sub_exact (by omega) (by norm_num [p,w32])
theorem add_canonical {a b : Nat} (ha : a<p) (hb : b<p) : subP (a+b)<p := by
  unfold subP; split_ifs <;> omega
theorem sub_canonical {a b : Nat} (ha : a<p) (hb : b<p) : subP (a+p-b)<p := by
  unfold subP; split_ifs <;> omega
theorem product_word_bound {a b : Nat} (ha : a<w32) (hb : b<w32) : a*b<w64 := by
  have h:=Nat.mul_le_mul (show a≤w32-1 by omega) (show b≤w32-1 by omega)
  have hm : (w32-1)*(w32-1)<w64 := by norm_num [w32,w64]
  exact lt_of_le_of_lt h hm
theorem mul_kernel_exact {a b : Nat} (ha : a<w32) (hb : b<w32) :
    (a*b)%w64=a*b := Nat.mod_eq_of_lt (product_word_bound ha hb)

-- Each reducer addition is safe for ANY u64, not only a field product.
-- Prior V5M31RawMulReduction proves mask/shift equals this div/mod fold.
def fold31 (x : Nat) := x%2147483648+x/2147483648
def fastFold31 (x : Nat) := wrapAdd w64 (x%2147483648) (x/2147483648)
theorem fold_bound {x : Nat} (h : x<w64) : fold31 x<w64 := by
  have hm:=Nat.mod_lt x (by decide : 0<2147483648)
  have hd : x/2147483648<8589934592 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).2
    norm_num [w64] at h ⊢
    exact h
  dsimp [fold31,w64]; omega
theorem fold_exact {x : Nat} (h : x<w64) : fastFold31 x=fold31 x :=
  wrap_add_exact (fold_bound h)
theorem two_folds_exact {x : Nat} (h : x<w64) :
    fastFold31 (fastFold31 x)=fold31 (fold31 x) := by
  rw [fold_exact h, fold_exact (fold_bound h)]
#print axioms add_kernel_exact
#print axioms sub_kernel_exact
#print axioms neg_kernel_exact
#print axioms add_canonical
#print axioms sub_canonical
#print axioms mul_kernel_exact
#print axioms two_folds_exact

theorem cm_mul_raw_exact {a b c d : Nat}
    (ha : a<p) (hb : b<p) (hc : c<p) (hd : d<p) :
    (wrapAdd w64 a b * wrapAdd w64 c d)%w64=(a+b)*(c+d) := by
  have hw : w32<w64 := by norm_num [w32,w64]
  rw [wrap_add_exact ((add_word_bound ha hb).trans hw),
      wrap_add_exact ((add_word_bound hc hd).trans hw)]
  exact mul_kernel_exact (add_word_bound ha hb) (add_word_bound hc hd)

theorem cm_square_raw_exact {a b : Nat} (ha : a<p) (hb : b<p) :
    (wrapAdd w64 a b * wrapSub w64 (wrapAdd w64 a p) b)%w64 =
      (a+b)*(a+p-b) := by
  have hw : w32<w64 := by norm_num [w32,w64]
  obtain ⟨h0,h1,h2⟩:=sub_word_bounds ha hb
  rw [wrap_add_exact ((add_word_bound ha hb).trans hw),
      wrap_add_exact (h0.trans hw), wrap_sub_exact h1 (h0.trans hw)]
  exact mul_kernel_exact (add_word_bound ha hb) h2
#print axioms cm_mul_raw_exact
#print axioms cm_square_raw_exact

-- Local invariant for every product-channel update in a fixed group of ≤4.
def limbMax : Nat := p-1
theorem mac_exact {s a b : Nat} (h : s+a*b<w64) :
    wrapAdd w64 s ((a*b)%w64)=s+a*b := by
  rw [Nat.mod_eq_of_lt (show a*b<w64 by omega)]
  exact wrap_add_exact h
theorem four_mac_bound {s a b : Nat}
    (hs : s≤3*limbMax^2) (ha : a≤limbMax) (hb : b≤limbMax) :
    s+a*b<w64 := by
  have hp : a*b≤limbMax^2 := by
    simpa [pow_two] using Nat.mul_le_mul ha hb
  have hm : 4*limbMax^2<w64 := by norm_num [limbMax,p,w64]
  omega
theorem four_mac_exact {s a b : Nat}
    (hs : s≤3*limbMax^2) (ha : a≤limbMax) (hb : b≤limbMax) :
    wrapAdd w64 s ((a*b)%w64)=s+a*b :=
  mac_exact (four_mac_bound hs ha hb)

-- The affine kernel has THREE products, followed by at most four raw limbs.
-- It never adds those constants to the four-product accumulator.
theorem affine_add_bound {s c : Nat}
    (hs : s≤3*limbMax^2) (hc : c≤4*limbMax) : s+c<w64 := by
  have hm : 3*limbMax^2+4*limbMax<w64 := by norm_num [limbMax,p,w64]
  omega
theorem affine_add_exact {s c : Nat}
    (hs : s≤3*limbMax^2) (hc : c≤4*limbMax) :
    wrapAdd w64 s c=s+c := wrap_add_exact (affine_add_bound hs hc)
#print axioms four_mac_exact
#print axioms affine_add_exact

theorem schoolbook_real_range {a b c d : Nat}
    (ha : a<p) (hb : b<p) (hc : c<p) (hd : d<p) :
    b*d≤a*c+p^2 ∧ a*c+p^2<w64 ∧ a*c+p^2-b*d<w64 := by
  have ac : a*c≤(p-1)^2 := by
    simpa [pow_two] using Nat.mul_le_mul (show a≤p-1 by omega) (show c≤p-1 by omega)
  have bd : b*d≤(p-1)^2 := by
    simpa [pow_two] using Nat.mul_le_mul (show b≤p-1 by omega) (show d≤p-1 by omega)
  have hp : (p-1)^2<p^2 := by norm_num [p]
  have hw : (p-1)^2+p^2<w64 := by norm_num [p,w64]
  omega
theorem schoolbook_imag_range {a b c d : Nat}
    (ha : a<p) (hb : b<p) (hc : c<p) (hd : d<p) : a*d+b*c<w64 := by
  have ad : a*d≤(p-1)^2 := by
    simpa [pow_two] using Nat.mul_le_mul (show a≤p-1 by omega) (show d≤p-1 by omega)
  have bc : b*c≤(p-1)^2 := by
    simpa [pow_two] using Nat.mul_le_mul (show b≤p-1 by omega) (show c≤p-1 by omega)
  have hw : 2*(p-1)^2<w64 := by norm_num [p,w64]
  omega
theorem schoolbook_real_mod (a b c d : Int) :
    (a*c+(p:Int)^2-b*d)%(p:Int)=(a*c-b*d)%(p:Int) := by
  simp [pow_two,Int.sub_emod,Int.add_emod,Int.mul_emod]
theorem karatsuba_imag {K : Type*} [CommRing K] (a b c d : K) :
    (a+b)*(c+d)-a*c-b*d=a*d+b*c := by ring
#print axioms schoolbook_real_range
#print axioms schoolbook_imag_range
#print axioms schoolbook_real_mod
#print axioms karatsuba_imag

-- Branchless canonicalisation of the exact small add/sub intermediate.
-- The bit implementation uses the earlier mask/shift-to-mod/div bridge.
def branchlessSmall (s : Nat) := (s+(s+1)/2147483648)%2147483648
theorem branchless_small_exact {s : Nat} (hs : s<2*p) :
    branchlessSmall s=subP s := by
  unfold branchlessSmall subP
  dsimp [p] at *
  split_ifs <;> omega
theorem branchless_small_range {s : Nat} (hs : s<2*p) :
    s+1<w32 ∧ s+(s+1)/2147483648<w32 := by
  dsimp [p,w32] at *
  omega
#print axioms branchless_small_exact
#print axioms branchless_small_range
end AspisV8.M31Range
