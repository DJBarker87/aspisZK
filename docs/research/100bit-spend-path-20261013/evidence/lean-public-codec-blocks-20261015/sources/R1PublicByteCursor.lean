import Mathlib.Data.List.OfFn

/-! A small list cursor for public byte codecs. It describes a mathematical
prefix decode and leaves source parsing correspondence to separate results. -/
set_option autoImplicit false

namespace AspisR1.PublicByteCursor

abbrev Byte := Fin 256

def read {A : Type} (n : Nat) (decode : List Byte → Option A)
    (bytes : List Byte) : Option (A × List Byte) :=
  (decode (bytes.take n)).map (fun a => (a, bytes.drop n))

theorem read_encoded {A : Type} (n : Nat) (decode : List Byte → Option A)
    (encode : A → List Byte) (a : A) (tail : List Byte)
    (hlen : ∀ x, (encode x).length = n)
    (hround : ∀ x, decode (encode x) = some x) :
    read n decode (encode a ++ tail) = some (a, tail) := by
  have htake : (encode a ++ tail).take n = encode a := by
    rw [List.take_append_of_le_length (by rw [hlen a]),
      List.take_of_length_le (by rw [hlen a])]
  have hdrop : (encode a ++ tail).drop n = tail := by
    rw [List.drop_append_of_le_length (by rw [hlen a]),
      List.drop_of_length_le (by rw [hlen a]), List.nil_append]
  simp [read, htake, hdrop, hround a]

theorem read_sound {A : Type} (n : Nat) (decode : List Byte → Option A)
    (encode : A → List Byte) (bytes : List Byte) (a : A) (rest : List Byte)
    (hback : ∀ bs x, decode bs = some x → encode x = bs)
    (hread : read n decode bytes = some (a, rest)) :
    bytes = encode a ++ rest := by
  unfold read at hread
  cases hd : decode (bytes.take n) with
  | none => simp [hd] at hread
  | some value =>
      have hpair : (value, bytes.drop n) = (a, rest) := by
        simpa [hd] using hread
      have hvalue : value = a := congrArg Prod.fst hpair
      have hrest : bytes.drop n = rest := congrArg Prod.snd hpair
      have hdecode : decode (bytes.take n) = some a := by
        simpa [hvalue] using hd
      have henc := hback (bytes.take n) a hdecode
      calc
        bytes = bytes.take n ++ bytes.drop n := (List.take_append_drop n bytes).symm
        _ = encode a ++ bytes.drop n := by rw [← henc]
        _ = encode a ++ rest := by rw [hrest]

#print axioms read_encoded
#print axioms read_sound

end AspisR1.PublicByteCursor
