import KMX_CopyMeaning
import NJE_RoundTrace

set_option autoImplicit false
namespace NJP_CopyFrame

/-- A selected-byte certificate is universally quantified; it identifies the
entire window, without fixing or zeroing any unobserved source byte. -/
theorem window_ext {α : Type} (source : Nat → α) (window : Fin 32 → α)
    (offset : Nat) (selected : ∀ j, window j=source (offset+j.val)) :
    window=fun j => source (offset+j.val) := funext selected

/-- Complete 16-by-32 mutable digest frame, assembled from independent row/byte
certificates. Both selected indices are arbitrary in each native branch cut. -/
theorem digest_write_ext {α : Type} (before after : Fin 16 → Fin 32 → α)
    (w : Fin 16) (reply : Fin 32 → α)
    (selected : ∀ k j, after k j=if k=w then reply j else before k j) :
    after=fun k j => if k=w then reply j else before k j := by
 funext k j
 exact selected k j

/-- Native writes of one digest instantiate the exact KMX value law on the
flat byte carrier. Disjoint bytes are framed for every allocation length. -/
theorem flat_window {α : Type} (src dst : Nat → α) (offset k : Nat) :
    KMX_CopyMeaning.loop src dst offset 32 k=
      if offset≤k ∧ k<offset+32 then src k else dst k :=
 KMX_CopyMeaning.loop_spec src dst offset 32 k

theorem outside {α : Type} (src dst : Nat → α) (offset k : Nat)
    (disjoint : k<offset ∨ offset+32≤k) :
    KMX_CopyMeaning.loop src dst offset 32 k=dst k :=
 KMX_CopyMeaning.copy_frame src dst offset 32 k disjoint

/-- Coordinate and row views of a flat 16-digest allocation are disjoint. -/
theorem different_row (w k : Fin 16) (j : Fin 32) (different : k≠w) :
    32*k.val+j.val<32*w.val ∨ 32*w.val+32≤32*k.val+j.val := by
 have neq : k.val≠w.val := fun eq => different (Fin.ext eq)
 omega

/-- The upper bound is derived from the full MAX_BATCH/LEAF_BITS domain,
not the predecessor's 96-byte allocation. -/
theorem caller_range (count : Nat) (bounded : count≤16*18) : 32*count≤9216 := by omega

#print window_ext
#print axioms window_ext
#print digest_write_ext
#print axioms digest_write_ext
#print flat_window
#print axioms flat_window
#print outside
#print axioms outside
#print different_row
#print axioms different_row
#print caller_range
#print axioms caller_range
end NJP_CopyFrame
