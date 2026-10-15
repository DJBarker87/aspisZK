import R1RawRoundDecode

/-! Structural append and prefix laws for the raw-round encoder. These are
list-plumbing facts and do not assert transcript or source correspondence. -/
set_option autoImplicit false

namespace AspisR1.RawRoundEncodeAppend

open AspisR1.InitialWalk FS2.Duplex

variable {M Cv : Type} {L : Nat}

theorem encode_append (p : FS2.Duplex.Params M Cv L) (j : Nat)
    (left right : List (Rec M)) :
    RawRoundDecode.encode p j (left ++ right) =
      RawRoundDecode.encode p j left ++
        RawRoundDecode.encode p (j + left.length) right := by
  induction left generalizing j with
  | nil => simp [RawRoundDecode.encode]
  | cons r left ih =>
      simp only [List.cons_append, RawRoundDecode.encode]
      rw [ih (j + 1)]
      have hoff : j + (r :: left).length = j + 1 + left.length := by
        simp only [List.length_cons]
        omega
      rw [hoff]

theorem encode_take (p : FS2.Duplex.Params M Cv L) (j : Nat)
    (rs : List (Rec M)) (n : Nat) :
    (RawRoundDecode.encode p j rs).take n =
      RawRoundDecode.encode p j (rs.take n) := by
  induction rs generalizing j n with
  | nil => simp [RawRoundDecode.encode]
  | cons r rs ih =>
      cases n with
      | zero => simp [RawRoundDecode.encode]
      | succ n =>
          simp only [List.take_succ_cons, RawRoundDecode.encode]
          rw [ih (j + 1) n]

#print axioms encode_append
#print axioms encode_take

end AspisR1.RawRoundEncodeAppend
