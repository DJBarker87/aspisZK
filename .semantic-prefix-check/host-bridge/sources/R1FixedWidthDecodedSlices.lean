import R1FixedWidthDecoder
import R1FixedWidthSlice
import R1FixedWidthReconstruction

/-! Relate recursive fixed-width parsing to its exact per-offset reads. -/
set_option autoImplicit false

namespace AspisR1.FixedWidthDecodedSlices

open AspisR1.FixedWidthDecoder

private theorem encode_length {B A : Type} (f : A → List B) (k n : Nat)
    (xs : Fin n → A) (hlen : ∀ a, (f a).length = k) :
    (encode f xs).length = n * k := by
  induction n with
  | zero => simp [encode]
  | succ n ih =>
      let tail : Fin n → A := fun i => xs i.succ
      have henc : encode f xs = f (xs 0) ++ encode f tail := by
        simp [encode, tail, List.ofFn_succ, List.flatMap_cons]
      rw [henc, List.length_append, hlen (xs 0), ih tail]
      simp [Nat.succ_mul, Nat.add_comm]

theorem decode_eq_some_iff {B A : Type} (d : List B → Option A) (f : A → List B)
    (k n : Nat) (bytes : List B) (xs : Fin n → A)
    (hlen : ∀ a, (f a).length = k)
    (hround : ∀ a, d (f a) = some a)
    (hback : ∀ bs a, d bs = some a → f a = bs) :
    decode d k n bytes = some xs ↔
      bytes.length = n * k ∧
        ∀ i : Fin n, d ((bytes.drop (k * i.val)).take k) = some (xs i) := by
  constructor
  · intro hsuccess
    have hencode : encode f xs = bytes := encode_of_decode d f k n bytes xs hsuccess hback
    constructor
    · rw [← hencode]
      exact encode_length f k n xs hlen
    · intro i
      have hs := AspisR1.FixedWidthSlice.ofFn_flatMap_slice n f k hlen xs i
      change ((encode f xs).drop (k * i.val)).take k = f (xs i) at hs
      rw [hencode] at hs
      rw [hs, hround]
  · rintro ⟨hbytes, hreads⟩
    have hblocks : ∀ i : Fin n,
        f (xs i) = (bytes.drop (k * i.val)).take k := by
      intro i
      exact hback _ _ (hreads i)
    have hencode : encode f xs = bytes := by
      unfold encode
      rw [List.flatMap_def, List.map_ofFn]
      change (List.ofFn (fun i : Fin n => f (xs i))).flatten = bytes
      rw [show List.ofFn (fun i : Fin n => f (xs i)) =
          List.ofFn (fun i : Fin n => (bytes.drop (k * i.val)).take k) by
            apply congrArg List.ofFn
            funext i
            exact hblocks i]
      exact AspisR1.FixedWidthReconstruction.slices_flatten bytes k n hbytes
    rw [← hencode]
    exact decode_encode d f k n xs hlen hround

#print axioms decode_eq_some_iff

end AspisR1.FixedWidthDecodedSlices
