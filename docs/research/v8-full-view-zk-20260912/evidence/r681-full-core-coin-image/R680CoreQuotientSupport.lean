import AspisV8R19.R574SparseGCorePolynomial
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R680CoreQuotientSupport
open AspisR19.SparseGCoreInverse AspisV8R19.R574SparseGCorePolynomial
variable {F : Type*} [Field F] [NeZero (2 : F)]

lemma channel_extend_high (x : Fin 271 → F) (d k : Nat) (hd : 235 ≤ d) :
    channel (extend x) d k = 0 := by
  unfold channel
  have h32 : ¬ d < 32 := by omega
  rw [if_neg h32]
  simp only
  split_ifs with hm hk1 hk3 hk2 hk1
  all_goals try {rfl}
  all_goals unfold extend
  all_goals rw [dif_neg (by omega)]

theorem weightedQ_support (alpha : F) (x : Fin 271 → F) (r : Nat) (hr : 940 ≤ r) :
    weightedQ alpha x r = 0 := by
  have hd : 235 ≤ r / 4 := by omega
  unfold weightedQ nz ch
  split_ifs with h
  · rw [channel_extend_high x (r/4) 1 hd, channel_extend_high x (r/4) 2 hd,
      channel_extend_high x (r/4) 3 hd]
    ring
  · rw [channel_extend_high x (r/4) (r%4) hd]
    ring
#print axioms weightedQ_support
end AspisV8R19.R680CoreQuotientSupport
