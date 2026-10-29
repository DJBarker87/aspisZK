import R1Z.PV_RDCD4_LazyPair
import R1Z.PV_RDCD4_LazyChannels
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_LazyAccumulate
open Aeneas Aeneas.Std Result PV_RDCD4_LazyComponents PV_RDCD4_LazyCell
/-- Complete source control for one product's nine channels. All state is owned. -/
def source (sums : Sums) (left right : Q) : Result Sums := do
  let (l,r) ← PV_RDCD4_LazyPair.pair left right
  PV_RDCD4_LazyChannels.nine l r sums

def reference (sums : Sums) (left right : Q) : Result Sums := do
  let (l,r) ← PV_RDCD4_LazyPair.pair left right
  let s ← cell l r sums 0 0
  let s ← cell l r s 0 1
  let s ← cell l r s 0 2
  let s ← cell l r s 1 0
  let s ← cell l r s 1 1
  let s ← cell l r s 1 2
  let s ← cell l r s 2 0
  let s ← cell l r s 2 1
  cell l r s 2 2

theorem binding (sums : Sums) (left right : Q) :
    source sums left right = reference sums left right := by
  unfold source reference
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨l,r⟩ _
  simp only [Aeneas.Std.uncurry,PV_RDCD4_LazyChannels.nine_unroll,
    PV_RDCD4_LazyChannels.row_unroll,bind_assoc_eq]
#print axioms binding
end R1Z.PV_RDCD4_LazyAccumulate
