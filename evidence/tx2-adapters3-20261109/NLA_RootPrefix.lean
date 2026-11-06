import NKP_LaneCompletion
set_option autoImplicit false
noncomputable section
namespace NLA_RootPrefix
open Aeneas Aeneas.Std Result
abbrev Node := NKP_LaneCuts.Node
abbrev PE := NKF_BoxModel.PE
/-- The root decoder precedes every frontier call. Outer fail/div retain
runtime partiality; inner errors map exactly to InvalidAccountData. -/
def enter {F A : Type} (reply : Result (core.result.Result Node F))
 (next : Node → Result A) : Result (core.result.Result A PE) := do
 match ← reply with
 | .Err _ => ok (.Err .InvalidAccountData)
 | .Ok root => return .Ok (← next root)

theorem rejected {F A : Type} (e : F) (next : Node → Result A) :
 enter (ok (.Err e)) next = ok (.Err .InvalidAccountData) := rfl

theorem returned {F A : Type} (root : Node) (next : Node → Result A) :
 @enter F A (ok (.Ok root)) next = do return .Ok (← next root) := rfl

theorem abort {F A : Type} (e : Error) (next : Node → Result A) :
 @enter F A (.fail e) next = .fail e := rfl

theorem diverge {F A : Type} (next : Node → Result A) :
 @enter F A .div next = .div := rfl

/-- The byte projection is uniformly quantified at the SAME call; every
coordinate reconstructs the input, rather than selecting separate replies. -/
theorem same_window (input tree : Fin 32 → U8)
 (cut : ∀ i, input i = tree i) : input = tree := funext cut

theorem absolute_root (byte : Nat) (small : byte < 32) :
 80 + (16 + byte) = 96 + byte ∧ 96 + byte < 128 := by omega

/-- The root failure is an exact prefix, independent of any later frontier
oracle. This does not assert a frozen producer or an allocation law. -/
theorem error_suffix_independent {F A : Type} (e : F)
 (next₁ next₂ : Node → Result A) :
 enter (ok (.Err e)) next₁ = enter (ok (.Err e)) next₂ := rfl

#print axioms rejected
#print axioms returned
#print axioms abort
#print axioms diverge
#print axioms same_window
#print axioms absolute_root
#print axioms error_suffix_independent
end NLA_RootPrefix
