import NMC_HeapLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Parent
open Aeneas Aeneas.Std Result
/-- Claims layout is inherited from CLOSED129's exact1392-byte/alignment4
packet; other regions retain arbitrary layout and initializedness. -/
def extent : Region→Nat
 | .raw _ size _ _=>size
 | .claims _=>1392
def alignment : Region→Nat
 | .raw _ _ align _=>align
 | .claims _=>4
def base (identity : Nat) : Region→Nat
 | .raw address _ _ _=>address
 | .claims _=>identity
/-- Every bit of an unrelated raw region, including uninitialized cells and
metadata, survives allocation and error cleanup of the owned Claims box. -/
theorem raw_frame (heap : Heap) (owner address rawBase size align : Nat)
 (bytes : Nat→Option U8) (value : Option Claims)
 (before : heap address=some (.raw rawBase size align bytes)) (disjoint : address≠owner) :
 write heap owner value address=some (.raw rawBase size align bytes) :=
 (write_frame heap owner address value disjoint).trans before
theorem claims_layout (heap : Heap) (owner : Nat) (value : Claims) :
 write heap owner (some value) owner=some (.claims value) ∧
 extent (.claims value)=1392 ∧ alignment (.claims value)=4 ∧ base owner (.claims value)=owner := by
 exact ⟨write_owner heap owner (some value),rfl,rfl,rfl⟩
#print axioms raw_frame
#print axioms claims_layout
end AspisR1.NMC_Parent
end
