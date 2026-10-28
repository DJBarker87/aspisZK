import PV_L2C_DigestList
set_option autoImplicit false
namespace PV_L2C_AccountLayout
open Aeneas Aeneas.Std Result PV_L2C_DigestList

/-- Tree account root, followed by all twenty frontier digests, occupies the
complete 16..688 field region. No active/inactive frontier selection occurs. -/
def offset (j : Nat) : Nat := 16+32*j

theorem bounds (j : Nat) (hj : j < 21) : offset j + 32 ≤ 688 := by
  unfold offset;omega
#print axioms bounds

theorem frontier_offset (j : Nat) : offset (j+1) = 48+32*j := by
  unfold offset;omega
#print axioms frontier_offset

theorem lane_bounds (j : Nat) (hj : j < 21) :
    80+offset j+32 ≤ 768 := by
  have := bounds j hj;omega
#print axioms lane_bounds

theorem source_field (bytes : List Bytes) (ds : List Digest)
    (count : bytes.length = 21) (returned : run bytes = ok (.Ok ds)) (j : Fin 21) :
    ∃ d, ds[j.val]? = some d ∧ ∀ x ∈ d.val, x.val < 2147483647 :=
  field bytes ds returned j.val (by rw [count];exact j.isLt)
#print axioms source_field

/-- In particular, every active frontier slot has the same decode provenance
as every inactive slot; there is no bit-of-next-index hypothesis. -/
theorem frontier (bytes : List Bytes) (ds : List Digest)
    (count : bytes.length = 21) (returned : run bytes = ok (.Ok ds)) (j : Fin 20) :
    ∃ d, ds[j.val+1]? = some d ∧ ∀ x ∈ d.val, x.val < 2147483647 :=
  source_field bytes ds count returned ⟨j.val+1,by omega⟩
#print axioms frontier
end PV_L2C_AccountLayout
