import MultiproofConeCanonical
import R1FixedWidthDecoder
set_option autoImplicit false
namespace AspisR1.S4CanonicalBlocksV1
open OraclePortCompactDraft AspisV8R19.DuplexFrames
open AspisR1.MultiproofConeCanonical

theorem canonical_split_blocks (n : Nat) (bs : Bytes) (hc : canonical bs) :
    canonical (bs.take (4*n)) ∧ canonical (bs.drop (4*n)) := by
  induction n generalizing bs with
  | zero => simpa [canonical] using hc
  | succ n ih =>
    cases bs with
    | nil => simp [canonical]
    | cons a bs =>
      cases bs with
      | nil => simp [canonical] at hc
      | cons b bs =>
        cases bs with
        | nil => simp [canonical] at hc
        | cons c bs =>
          cases bs with
          | nil => simp [canonical] at hc
          | cons d bs =>
            obtain ⟨hfirst, htail⟩ := (canonical_four a b c d bs).mp hc
            obtain ⟨htake, hdrop⟩ := ih bs htail
            have hn : 4*(n+1) = 4*n+1+1+1+1 := by omega
            rw [hn]
            simp only [List.take_succ_cons, List.drop_succ_cons]
            exact ⟨(canonical_four a b c d _).mpr ⟨hfirst, htake⟩, hdrop⟩

/-- Fixed-width completeness is structural and never unfolds a concrete 26-lane recurrence. -/
theorem decode_exists {B A : Type} (d : List B → Option A) (k n : Nat)
    (P : List B → Prop) (bs : List B) (hlen : bs.length = k*n) (hp : P bs)
    (hsplit : ∀ xs m, xs.length = k*(m+1) → P xs → P (xs.take k) ∧ P (xs.drop k))
    (hhead : ∀ xs, xs.length = k → P xs → ∃ a, d xs = some a) :
    ∃ values, FixedWidthDecoder.decode d k n bs = some values := by
  induction n generalizing bs with
  | zero =>
    have hb : bs = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
    subst bs
    exact ⟨Fin.elim0, by simp [FixedWidthDecoder.decode]⟩
  | succ n ih =>
    obtain ⟨ph, pt⟩ := hsplit bs n hlen hp
    have hk : k ≤ bs.length := by omega
    have hh : (bs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
    obtain ⟨head, hdecode⟩ := hhead (bs.take k) hh ph
    have ht : (bs.drop k).length = k*n := by simp only [List.length_drop]; omega
    obtain ⟨tail, htail⟩ := ih (bs.drop k) ht pt
    exact ⟨Fin.cons head tail, by simp [FixedWidthDecoder.decode, hdecode, htail]⟩
#print axioms canonical_split_blocks
#print axioms decode_exists
end AspisR1.S4CanonicalBlocksV1
