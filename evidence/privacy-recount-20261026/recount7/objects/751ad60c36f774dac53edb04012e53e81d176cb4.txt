import R0Z.PoseidonRefine

/-! Poseidon refinement, internal round (DESIGN-BUILDER-MODEL §11.4 c).

`internal_round_lift`: the extracted copy's `internal_round s c0 shifts`
returns `ok t` and every lane of `t` lifts to R0P's `poseidonInternalRound`
of the lifted state and constant, for every u32 state and constant, given
two named facts about the shift row (`ShiftsBound`, `ShiftsOk`; they are
the table-correspondence obligation for INTERNAL_SHIFTS and are not
evaluated here).  The part sum is related to R0P's ordered `foldl` over
`List.ofFn` by a generic `ofFn`/`range'` lemma, not by unfolding 15 cells. -/
set_option autoImplicit false

namespace R0Z.PoseidonRefine
open Aeneas Aeneas.Std Result R0PoseidonCopy R0Z.WriterRefine

theorem v15 : (15#usize : Usize).val = 15 := by simp

theorem usub (a b : Usize) (h : b.val ≤ a.val) : (Usize.wrapping_sub a b).val = a.val - b.val := by
  rw [Usize.wrapping_sub_val_eq]
  have ha : a.val < UScalar.size .Usize := by rw [UScalar.size_def]; exact a.hBounds
  rw [show a.val + (UScalar.size .Usize - b.val) = (a.val - b.val) + UScalar.size .Usize by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem sub64 (x y : U64) (h : y.val ≤ x.val) : (U64.wrapping_sub x y).val = x.val - y.val := by
  rw [U64.wrapping_sub_val_eq, size64]
  have hx : x.val < 18446744073709551616 := by
    have := x.hBounds; rw [show UScalarTy.U64.numBits = 64 from rfl] at this; exact this
  rw [show x.val + (18446744073709551616 - y.val) = (x.val - y.val) + 18446744073709551616 by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem shl64 (x : U64) (sh : U32) (hx : x.val < 4294967296) (hs : sh.val ≤ 16) :
    (U64.wrapping_shl x sh).val = x.val * 2 ^ sh.val := by
  show (U64.wrapping_shl x sh).bv.toNat = x.bv.toNat * 2 ^ sh.val
  rw [U64.wrapping_shl_bv_eq, show sh.val % 64 = sh.val by omega]
  show (x.bv <<< sh.val).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have h1 : x.bv.toNat * 2 ^ sh.val ≤ x.bv.toNat * 2 ^ 16 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hs)
  have h2 : x.bv.toNat * 2 ^ 16 < 4294967296 * 2 ^ 16 :=
    Nat.mul_lt_mul_of_pos_right hx (by norm_num)
  have h3 : (4294967296 * 2 ^ 16 : Nat) < 2 ^ 64 := by norm_num
  omega

theorem lane_val (full x sh : U32) (hs : sh.val ≤ 16) :
    (U64.wrapping_add (UScalar.cast .U64 full) (U64.wrapping_shl (UScalar.cast .U64 x) sh)).val =
      full.val + x.val * 2 ^ sh.val := by
  have hsh := shl64 (UScalar.cast .U64 x) sh (by rw [c64]; exact u32lt x) hs
  rw [c64] at hsh
  have h1 : x.val * 2 ^ sh.val ≤ x.val * 2 ^ 16 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hs)
  have h2 : x.val * 2 ^ 16 < 4294967296 * 2 ^ 16 := Nat.mul_lt_mul_of_pos_right (u32lt x) (by norm_num)
  have h3 : (4294967296 * 2 ^ 16 : Nat) + 4294967296 < 18446744073709551616 := by norm_num
  have := u32lt full
  exact add64v _ _ _ _ (c64 full) hsh (by omega)

theorem lane0_val (part s0 : U32) (h : s0.val ≤ part.val + 2147483647) :
    (U64.wrapping_sub (U64.wrapping_add (UScalar.cast .U64 part) (UScalar.cast .U64 P))
      (UScalar.cast .U64 s0)).val = part.val + 2147483647 - s0.val := by
  have hadd := add64v _ _ _ _ (c64 part) p64 (by have := u32lt part; omega)
  rw [sub64 _ _ (by rw [hadd, c64]; exact h), hadd, c64]

theorem canon_mod (x : U64) :
    (UScalar.cast .U32 (⟨BitVec.umod x.bv (UScalar.cast .U64 P).bv⟩ : U64)).val < 2147483647 := by
  have hm : (⟨BitVec.umod x.bv (UScalar.cast .U64 P).bv⟩ : U64).val = x.val % 2147483647 := by
    rw [umod_val, p64]
  have hlt : x.val % 2147483647 < 2147483647 := Nat.mod_lt _ (by omega)
  rw [c32 _ (by rw [hm]; omega), hm]
  exact hlt

theorem mul_canon (a b : U32) : ∃ z, m31_mul a b = ok z ∧ z.val < 2147483647 := by
  rw [m31_mul]
  simp only [lift, bind_tc_ok, remP]
  exact ⟨_, rfl, canon_mod _⟩

theorem pow5_canon (x z : U32) (h : pow5 x = ok z) : z.val < 2147483647 := by
  obtain ⟨s1, hs1, -⟩ := mul_canon x x
  obtain ⟨s2, hs2, -⟩ := mul_canon s1 s1
  obtain ⟨s3, hs3, hc⟩ := mul_canon s2 x
  have e : pow5 x = ok s3 := by
    rw [pow5, hs1]; simp only [bind_tc_ok]; rw [hs2]; simp only [bind_tc_ok]; exact hs3
  rw [e] at h
  injection h with h'
  rw [← h']
  exact hc

theorem ofFn_range' {α : Type} : ∀ (n s : Nat) (f : Fin n → α) (g : Nat → α),
    (∀ i : Fin n, f i = g (s + i.val)) → List.ofFn f = (List.range' s n).map g
  | 0, s, f, g, _ => by rw [List.ofFn_zero]; rfl
  | n + 1, s, f, g, h => by
      rw [List.ofFn_succ, ofFn_range' n (s + 1) (fun i => f i.succ) g
        (fun i => by rw [h i.succ, Fin.val_succ, show s + (i.val + 1) = s + 1 + i.val by omega]),
        h 0, Fin.val_zero, Nat.add_zero]
      rfl

/-- The shift row's entries are at most 16 (so `x << shift` stays below 2^48). -/
def ShiftsBound (shifts : Array U32 15#usize) : Prop := ∀ j, j < 15 → (shifts.val[j]!).val ≤ 16

/-- The shift row equals R0P's `poseidonInternalShifts` (the INTERNAL_SHIFTS table obligation). -/
def ShiftsOk (shifts : Array U32 15#usize) : Prop :=
  ∀ j : Fin 15, (shifts.val[j.val]!).val = R0P.poseidonInternalShifts j

variable {K : Type} [Field K]

theorem lin_unfold (v : Fin 16 → K) (i : Fin 16) :
    R0P.poseidonInternalLinear v i =
      if h : i.val = 0 then (List.ofFn (fun j : Fin 15 => v j.succ)).foldl (· + ·) 0 - v 0
      else ((List.ofFn (fun j : Fin 15 => v j.succ)).foldl (· + ·) 0 + v 0) +
        v i * ((1 <<< R0P.poseidonInternalShifts ⟨i.val - 1, by have := i.isLt; omega⟩ : Nat) : K) :=
  rfl

variable [CharP K 0x7fffffff]

theorem part_loop (s : Array U32 16#usize) :
    ∀ (n : Nat) (i : Usize) (acc : U64), i.val + n = 16 →
      acc.val + n * 4294967296 < 18446744073709551616 →
      ∃ r, int_part_sum_loop s acc i = ok r ∧ r.val ≤ acc.val + n * 4294967296 ∧
        ((r.val : Nat) : K) = ((List.range' i.val n).map (liftN s)).foldl (· + ·) ((acc.val : Nat) : K)
  | 0, i, acc, h, _ => by
      refine ⟨acc, ?_, by omega, rfl⟩
      rw [int_part_sum_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, i, acc, h, hacc => by
      have hlt : i < 16#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : i.val < (16#usize).val := by rw [v16]; omega
      have hi1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      have hx := u32lt (s.val[i.val]!)
      have ha1 := add64v acc (UScalar.cast .U64 (s.val[i.val]!)) _ _ rfl (c64 _) (by omega)
      obtain ⟨r, hr, hrb, hrv⟩ := part_loop s n (Usize.wrapping_add i 1#usize)
        (U64.wrapping_add acc (UScalar.cast .U64 (s.val[i.val]!))) (by rw [hi1]; omega)
        (by rw [ha1]; omega)
      refine ⟨r, ?_, by rw [ha1] at hrb; omega, ?_⟩
      · rw [int_part_sum_loop, if_pos hlt]
        simp only [lift, bind_tc_ok, index_ok s i hb]
        exact hr
      · rw [hrv, hi1, ha1, Nat.cast_add]
        rfl

theorem part_lift (s : Array U32 16#usize) :
    ∃ part, int_part_sum s = ok part ∧ part.val < 2147483647 ∧
      liftU (K := K) part = (List.ofFn (fun j : Fin 15 => liftA (K := K) s j.succ)).foldl (· + ·) 0 := by
  have h0 : (0#u64 : U64).val = 0 := by simp
  obtain ⟨r, hr, -, hrv⟩ := part_loop (K := K) s 15 1#usize 0#u64 (by rw [z1]) (by rw [h0]; omega)
  have hof : List.ofFn (fun j : Fin 15 => liftA (K := K) s j.succ) = (List.range' 1 15).map (liftN s) :=
    ofFn_range' 15 1 _ _ (fun j => by
      show liftU (s.val[j.succ.val]!) = liftU (s.val[1 + j.val]!)
      rw [Fin.val_succ, Nat.add_comm])
  rw [int_part_sum]
  simp only [hr, lift, bind_tc_ok, remP]
  refine ⟨_, rfl, canon_mod _, ?_⟩
  rw [liftmod, hrv, z1, h0, Nat.cast_zero, hof]

theorem lin_loop (s : Array U32 16#usize) (shifts : Array U32 15#usize) (full : U32)
    (hsb : ShiftsBound shifts) :
    ∀ (n : Nat) (i : Usize) (out : Array U32 16#usize), i.val + n = 16 → 1 ≤ i.val →
      ∃ o, internal_linear_loop s shifts full out i = ok o ∧ ∀ k, k < 16 →
        (i.val ≤ k → liftU (K := K) (o.val[k]!) =
          liftU full + liftN s k * (2 : K) ^ (shifts.val[k - 1]!).val) ∧
        (k < i.val → o.val[k]! = out.val[k]!)
  | 0, i, out, h, _ => by
      refine ⟨out, ?_, fun k hk => ⟨fun h' => absurd h' (by omega), fun _ => rfl⟩⟩
      rw [internal_linear_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, i, out, h, h1 => by
      have hlt : i < 16#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : i.val < (16#usize).val := by rw [v16]; omega
      have hi1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      have hsub : (Usize.wrapping_sub i 1#usize).val = i.val - 1 := by
        rw [usub _ _ (by rw [z1]; omega), z1]
      have hsb' : (Usize.wrapping_sub i 1#usize).val < (15#usize).val := by rw [hsub, v15]; omega
      have step : ∃ X : U32, internal_linear_loop s shifts full out i =
          internal_linear_loop s shifts full (out.set i X) (Usize.wrapping_add i 1#usize) ∧
          liftU (K := K) X = liftU full + liftN s i.val * (2 : K) ^ (shifts.val[i.val - 1]!).val := by
        rw [internal_linear_loop, if_pos hlt]
        simp only [lift, bind_tc_ok, index_ok s i hb, index_ok shifts _ hsb', remP, update_ok out i _ hb]
        refine ⟨_, rfl, ?_⟩
        rw [liftmod, lane_val _ _ _ (hsb _ (by rw [hsub]; omega)), hsub]
        unfold liftN liftU
        push_cast
        rfl
      obtain ⟨X, hX, hXv⟩ := step
      obtain ⟨o, ho, hov⟩ := lin_loop s shifts full hsb n (Usize.wrapping_add i 1#usize) (out.set i X)
        (by rw [hi1]; omega) (by rw [hi1]; omega)
      refine ⟨o, by rw [hX]; exact ho, fun k hk => ⟨fun hik => ?_, fun hki => ?_⟩⟩
      · by_cases e : k = i.val
        · subst e
          rw [(hov i.val hk).2 (by rw [hi1]; omega), set_get' out i X hb i.val, if_pos rfl]
          exact hXv
        · exact (hov k hk).1 (by rw [hi1]; omega)
      · rw [(hov k hk).2 (by rw [hi1]; omega), set_get' out i X hb k, if_neg (by omega)]

/-- The internal linear layer of the copy lifts to R0P's `poseidonInternalLinear`
(lane 0 needs the canonical-lane-0 fact `h0`). -/
theorem internal_linear_lift (s : Array U32 16#usize) (shifts : Array U32 15#usize)
    (h0 : (s.val[0]!).val < 2147483647) (hsb : ShiftsBound shifts) (hsh : ShiftsOk shifts) :
    ∃ t, internal_linear s shifts = ok t ∧
      ∀ i : Fin 16, liftU (K := K) (t.val[i.val]!) = R0P.poseidonInternalLinear (liftA s) i := by
  obtain ⟨part, hp, hpc, hpv⟩ := part_lift (K := K) s
  obtain ⟨full, hf, hfv⟩ := add_lift (K := K) part (s.val[0]!)
  have hle : (s.val[0]!).val ≤ part.val + 2147483647 := by omega
  have hb0 : (0#usize : Usize).val < (16#usize).val := by rw [z0, v16]; omega
  have step : ∃ X0 : U32, internal_linear s shifts =
      internal_linear_loop s shifts full ((Array.repeat 16#usize 0#u32).set 0#usize X0) 1#usize ∧
      liftU (K := K) X0 = liftU part - liftU (s.val[0]!) := by
    rw [internal_linear]
    simp only [hp, lift, bind_tc_ok, index_ok s 0#usize hb0, z0, hf, remP, update_ok _ 0#usize _ hb0]
    refine ⟨_, rfl, ?_⟩
    rw [liftmod, lane0_val _ _ hle]
    unfold liftU
    rw [Nat.cast_sub hle, Nat.cast_add, CharP.cast_eq_zero K 0x7fffffff, add_zero]
  obtain ⟨X0, hX0, hX0v⟩ := step
  obtain ⟨o, ho, hov⟩ := lin_loop (K := K) s shifts full hsb 15 1#usize
    ((Array.repeat 16#usize 0#u32).set 0#usize X0) (by rw [z1]) (le_of_eq z1.symm)
  refine ⟨o, by rw [hX0]; exact ho, fun i => ?_⟩
  have hi := i.isLt
  by_cases hi0 : i.val = 0
  · rw [lin_unfold, dif_pos hi0, hi0, (hov 0 (by omega)).2 (lt_of_lt_of_eq Nat.zero_lt_one z1.symm),
      set_get' _ 0#usize X0 hb0 0, z0, if_pos rfl, hX0v, hpv]
    rfl
  · have hs := hsh ⟨i.val - 1, by omega⟩
    dsimp only at hs
    rw [lin_unfold, dif_neg hi0, (hov i.val hi).1 (by rw [z1]; omega), hfv, hpv, hs, Nat.shiftLeft_eq,
      Nat.one_mul, Nat.cast_pow, Nat.cast_ofNat]
    rfl

/-- **Single internal round.**  For every u32 state `s` and constant `c0`, and a
shift row satisfying the named table facts, the extracted copy's
`internal_round` returns `ok t` and every lane of `t` lifts to R0P's
`poseidonInternalRound` of the lifted state and constant. -/
theorem internal_round_lift (s : Array U32 16#usize) (c0 : U32) (shifts : Array U32 15#usize)
    (hsb : ShiftsBound shifts) (hsh : ShiftsOk shifts) :
    ∃ t, internal_round s c0 shifts = ok t ∧
      ∀ i : Fin 16, liftU (K := K) (t.val[i.val]!) =
        R0P.poseidonInternalRound (liftA s) (liftU c0) i := by
  have hb0 : (0#usize : Usize).val < (16#usize).val := by rw [z0, v16]; omega
  obtain ⟨z, hz, hzv⟩ := add_lift (K := K) (s.val[0]!) c0
  obtain ⟨y, hy, hyv⟩ := pow5_lift (K := K) z
  have hyc := pow5_canon z y hy
  have hset := set_get' s 0#usize y hb0
  have h0 : ((s.set 0#usize y).val[0]!).val < 2147483647 := by
    rw [hset 0, z0, if_pos rfl]; exact hyc
  obtain ⟨t, ht, htv⟩ := internal_linear_lift (K := K) (s.set 0#usize y) shifts h0 hsb hsh
  refine ⟨t, ?_, fun i => ?_⟩
  · rw [internal_round]
    simp only [index_ok s 0#usize hb0, z0, bind_tc_ok, hz, hy, update_ok s 0#usize y hb0]
    exact ht
  · rw [htv i]
    have hfun : liftA (K := K) (s.set 0#usize y) =
        fun lane => if lane = 0 then R0P.poseidonPow5 (liftA s 0 + liftU c0) else liftA s lane := by
      funext lane
      show liftU ((s.set 0#usize y).val[lane.val]!) = _
      rw [hset lane.val, z0]
      by_cases hl : lane = 0
      · have hv : lane.val = 0 := by rw [hl]; rfl
        rw [if_pos hv, if_pos hl, hyv, hzv]
        rfl
      · rw [if_neg (show ¬ (lane.val = 0) from fun h => hl (Fin.ext h)), if_neg hl]
        rfl
    rw [hfun]
    rfl

end R0Z.PoseidonRefine

#print axioms R0Z.PoseidonRefine.part_lift
#print axioms R0Z.PoseidonRefine.internal_linear_lift
#print axioms R0Z.PoseidonRefine.internal_round_lift
