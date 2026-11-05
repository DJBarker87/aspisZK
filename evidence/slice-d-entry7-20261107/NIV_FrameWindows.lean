import NIS_AbiFrame
set_option autoImplicit false
namespace NIV_FrameWindows

/-- Transcribes the arbitrary j<7 scalar lamport assertion replacing the
56-byte builtin memcmp in NIV_sdk::check. The native/config/source hashes
and the independent-cell fixture domain are listed in NIV_CERTIFICATES.md. -/
def wordCut {n : Nat} {Word : Type} (before after : Fin n → Word) : Prop :=
  ∀ j, after j = before j

/-- Generic extensional composition: no concrete large finite universe is
evaluated. A single arbitrary native word assertion gives the whole vector. -/
theorem complete {n : Nat} {Word : Type} (before after : Fin n → Word)
    (cut : wordCut before after) : after = before := funext cut

theorem coordinate {n : Nat} {Word : Type} (before after : Fin n → Word)
    (same : after = before) (j : Fin n) : after j = before j := congrFun same j

#print axioms complete
#print axioms coordinate
end NIV_FrameWindows
