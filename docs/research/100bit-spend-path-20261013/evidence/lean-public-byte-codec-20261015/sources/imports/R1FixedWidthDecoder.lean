import Mathlib.Data.List.OfFn

/-! Structural encoder/decoder facts for fixed-width list encodings. -/
set_option autoImplicit false

namespace AspisR1.FixedWidthDecoder

def decode {B A : Type} (d : List B → Option A) (k : Nat) :
    (n : Nat) → List B → Option (Fin n → A)
  | 0, bytes => if bytes.length = 0 then some Fin.elim0 else none
  | n + 1, bytes => do
      let head ← d (bytes.take k)
      let tail ← decode d k n (bytes.drop k)
      pure (Fin.cons head tail)

def encode {B A : Type} (f : A → List B) {n : Nat} (xs : Fin n → A) : List B :=
  (List.ofFn xs).flatMap f

theorem decode_encode {B A : Type} (d : List B → Option A) (f : A → List B)
    (k n : Nat) (xs : Fin n → A)
    (hlen : ∀ a, (f a).length = k)
    (hround : ∀ a, d (f a) = some a) :
    decode d k n (encode f xs) = some xs := by
  induction n with
  | zero =>
      have hxs : xs = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simp [decode, encode, hxs]
  | succ n ih =>
      let tail : Fin n → A := fun i => xs i.succ
      have hcons : Fin.cons (xs 0) tail = xs := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have henc : encode f xs = f (xs 0) ++ encode f tail := by
        simp [encode, tail, List.ofFn_succ, List.flatMap_cons]
      have htail := ih tail
      rw [henc]
      simp only [decode]
      rw [List.take_append_of_le_length (by rw [hlen (xs 0)]),
        List.take_of_length_le (by rw [hlen (xs 0)])]
      simp only [hround]
      rw [List.drop_append_of_le_length (by rw [hlen (xs 0)]),
        List.drop_of_length_le (by rw [hlen (xs 0)]), List.nil_append, htail]
      exact congrArg some hcons

theorem encode_of_decode {B A : Type} (d : List B → Option A) (f : A → List B)
    (k n : Nat) (bytes : List B) (xs : Fin n → A)
    (hsuccess : decode d k n bytes = some xs)
    (hback : ∀ bs a, d bs = some a → f a = bs) :
    encode f xs = bytes := by
  induction n generalizing bytes with
  | zero =>
      cases bytes with
      | nil => rfl
      | cons b bs => simp [decode] at hsuccess
  | succ n ih =>
      cases hhead : d (bytes.take k) with
      | none => simp [decode, hhead] at hsuccess
      | some head =>
          cases htail : decode d k n (bytes.drop k) with
          | none => simp [decode, hhead, htail] at hsuccess
          | some tail =>
              have hxs : Fin.cons head tail = xs := by
                simpa [decode, hhead, htail] using hsuccess
              have htailenc : encode f tail = bytes.drop k :=
                ih (bytes.drop k) tail htail
              have henc : encode f xs = f head ++ encode f tail := by
                rw [← hxs]
                simp [encode, List.ofFn_succ, List.flatMap_cons]
              rw [henc, hback (bytes.take k) head hhead, htailenc]
              exact List.take_append_drop k bytes

#print axioms decode_encode
#print axioms encode_of_decode

end AspisR1.FixedWidthDecoder
