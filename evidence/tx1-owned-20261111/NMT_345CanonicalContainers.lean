import NMT_345CanonicalTransfer
import NMT_345CanonicalWithdrawal
import NKR_DigestChildren
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
open AspisR1

theorem canonical_bool_members (d : Array U32 8#usize)
 (h : NFY_NBG_PaymentChecks.canonical d = true) : NJX_DigestCohort.dc d := by
 simpa [NFY_NBG_PaymentChecks.canonical,NJX_DigestCohort.dc,List.all_eq_true] using h

theorem canonical_fin_members (d : Array U32 8#usize)
 (h : NBD_DigestInduction.Canonical d) : NJX_DigestCohort.dc d := by
 intro x hx
 obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp hx
 have inside : i < 8 := by rw [← d.property]; exact hi
 have out := h ⟨i,inside⟩
 simpa only [← e] using out

theorem frontier_members (f : NBH_Frontier.Frontier)
 (h : NBH_Frontier.CanonicalFrom f 0) : ∀ d ∈ f.val,NJX_DigestCohort.dc d := by
 intro d hd
 obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp hd
 have inside : i < 20 := by rw [← f.property]; exact hi
 rw [← e]
 exact canonical_fin_members _ (h ⟨i,inside⟩ (Nat.zero_le _))
#print axioms canonical_bool_members
#print axioms canonical_fin_members
#print axioms frontier_members
end NMT_345
