
/-- The tag dispatch of the two emissions agrees on every tag other than 7. -/
theorem match_carry {R : Type} (A B C D X : R) (i : Std.U8) (hi : i ≠ 7#u8) :
    (match (generalizing := false) i with | 4#uscalar => A | 5#uscalar => B | 6#uscalar => C | 7#uscalar => X | _ => D)
      = (match (generalizing := false) i with | 4#uscalar => A | 5#uscalar => B | 6#uscalar => C | _ => D) := by
  split <;> split <;> first | rfl | (exfalso; simp_all; done) | (exfalso; simp_all; exact hi (by decide)) | (exfalso; simp_all; exact hi rfl)

/-- On every data slice whose head byte (as the emitted code computes it, `copied (first data)`) is not 7, the 271869c946d process equals the 4bb3b3f process. -/
theorem process_carry (eqf : Slice Std.U8 → Array Std.U8 2#usize → Result Bool)
  (first : Slice Std.U8 → Result (Option Std.U8)) (copied : Option Std.U8 → Result (Option Std.U8))
  (c1 c2 c3 c4 c5 cc : Pk → Slice Acc → Slice Std.U8 → Result (core.result.Result Unit PE))
  (program_id : Pk) (accounts : Slice Acc) (data : Slice Std.U8)
  (h : ∀ r, (do let o ← first data; copied o) = ok r → r ≠ some 7#u8) :
  processNew eqf first copied c1 c2 c3 c4 c5 cc program_id accounts data
    = processOld eqf first copied c1 c2 c3 c4 c5 program_id accounts data := by
  unfold processNew processOld
  cases hf : first data with
  | ok o =>
    try simp only [Aeneas.Std.bind_tc_ok]
    cases hc : copied o with
    | ok o1 =>
      have hr : o1 ≠ some 7#u8 := h o1 (by rw [hf]; exact hc)
      try simp only [Aeneas.Std.bind_tc_ok]
      cases o1 with
      | none => rfl
      | some i =>
        have hi : i ≠ 7#u8 := fun e => hr (by rw [e])
        exact match_carry _ _ _ _ _ i hi
    | fail e => first | rfl | simp
    | div => first | rfl | simp
  | fail e => rfl
  | div => rfl
