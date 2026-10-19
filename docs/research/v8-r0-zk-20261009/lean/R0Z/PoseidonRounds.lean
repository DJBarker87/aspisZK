import R0Z.PoseidonConstLift
import R0Z.BlockRefine

/-! Poseidon refinement, composition (DESIGN-BUILDER-MODEL §11.5 (2), (3)).

`apply_round_lift`: the copy's `apply_round s r` lifts to R0P's
`poseidonApplyRound r` for every r < 22 (the three branches use
full_round_lift / internal_round_lift and the generated constant lifts).
`leading_pair_lift`: absorb loop, leading external layer and rounds 0, 1.
`perm_rounds_lift`: under `EndsLift pre absorb B`, `perm_rounds pre absorb`
returns rounds with `RoundsOk rounds B` — the loop invariant is that rows
0..k-1 lift to `blockIter B (r+1)` and the running state to `blockIter B k`. -/
set_option autoImplicit false

namespace R0Z.PoseidonRefine
open Aeneas Aeneas.Std Result R0PoseidonCopy R0Z.WriterRefine

/-! ### Generic array plumbing -/

theorem update_ok_a {α : Type} {n : Usize} (v : Array α n) (i : Usize) (x : α) (h : i.val < n.val) :
    Array.update v i x = ok (v.set i x) := by
  unfold Array.update
  have hl : i.val < v.val.length := by rw [v.property]; exact h
  rw [Array.getElem?_Usize_eq, List.getElem?_eq_getElem hl]
  rfl

theorem set_get_a {α : Type} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize) (x : α)
    (hi : i.val < n.val) (k : Nat) :
    (v.set i x).val[k]! = if k = i.val then x else v.val[k]! := by
  rw [Array.set_val_eq]
  have hl : i.val < v.val.length := by rw [v.property]; exact hi
  by_cases hk : k = i.val
  · subst hk
    rw [if_pos rfl, List.getElem!_eq_getElem?_getD, List.getElem?_set_self hl]
    rfl
  · rw [if_neg hk, List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm hk)]

theorem v11 : (11#usize : Usize).val = 11 := by simp
theorem v14 : (14#usize : Usize).val = 14 := by simp
theorem v18 : (18#usize : Usize).val = 18 := by simp

variable {K : Type} [Field K]

/-! ### R0P-side unfoldings (no constant is read) -/

theorem ar_init (rr : Fin 22) (h : rr.val < 4) (v : Fin 16 → K) :
    R0P.poseidonApplyRound rr v = R0P.poseidonFullRound v (R0P.poseidonExternalInitial ⟨rr.val, h⟩) := by
  unfold R0P.poseidonApplyRound
  exact dif_pos h

theorem ar_int (rr : Fin 22) (h4 : ¬ rr.val < 4) (h18 : rr.val < 4 + 14) (v : Fin 16 → K) :
    R0P.poseidonApplyRound rr v =
      R0P.poseidonInternalRound v (R0P.poseidonInternalConstants ⟨rr.val - 4, by omega⟩) := by
  unfold R0P.poseidonApplyRound
  rw [dif_neg h4, dif_pos h18]

theorem ar_fin (rr : Fin 22) (h4 : ¬ rr.val < 4) (h18 : ¬ rr.val < 4 + 14) (v : Fin 16 → K) :
    R0P.poseidonApplyRound rr v =
      R0P.poseidonFullRound v (R0P.poseidonExternalFinal ⟨rr.val - 4 - 14, by omega⟩) := by
  unfold R0P.poseidonApplyRound
  rw [dif_neg h4, dif_neg h18]

theorem trans_zero (h : 0 < 11) (s a : Fin 16 → K) :
    R0P.poseidonTransition ⟨0, h⟩ s a = R0P.poseidonLeadingPair s a := by
  unfold R0P.poseidonTransition
  exact if_pos rfl

theorem trans_succ (k : Nat) (hk : k < 11) (hk0 : k ≠ 0) (s a : Fin 16 → K) :
    R0P.poseidonTransition ⟨k, hk⟩ s a =
      R0P.poseidonApplyRound ⟨2 * k + 1, by omega⟩ (R0P.poseidonApplyRound ⟨2 * k, by omega⟩ s) := by
  unfold R0P.poseidonTransition
  exact if_neg hk0

theorem iter_zero (B : R0Z.BuilderModel.BlockIn K) : R0Z.BuilderModel.blockIter B 0 = B.pre := rfl

theorem iter_succ (B : R0Z.BuilderModel.BlockIn K) (k : Nat) (hk : k < 11) :
    R0Z.BuilderModel.blockIter B (k + 1) =
      R0P.poseidonTransition ⟨k, hk⟩ (R0Z.BuilderModel.blockIter B k) B.absorb := by
  first
  | exact dif_pos hk
  | simp only [R0Z.BuilderModel.blockIter, dif_pos hk]

variable [CharP K 0x7fffffff]

/-! ### apply_round -/

theorem apply_round_lift (s : Array U32 16#usize) (round : Usize) (hr : round.val < 22) :
    ∃ t, apply_round s round = ok t ∧
      liftA (K := K) t = R0P.poseidonApplyRound ⟨round.val, hr⟩ (liftA s) := by
  by_cases h4 : round.val < 4
  · have hlt : round < 4#usize := by rw [UScalar.lt_equiv]; scalar_tac
    have hb : round.val < (4#usize).val := by rw [v4]; exact h4
    obtain ⟨t, ht, htv⟩ := full_round_lift (K := K) s (EXTERNAL_INITIAL.val[round.val]!)
    refine ⟨t, ?_, ?_⟩
    · rw [apply_round, if_pos hlt, index_ok_gen EXTERNAL_INITIAL round hb]
      simp only [bind_tc_ok]
      exact ht
    · have e : liftA (K := K) t = _ := funext htv
      have ec : liftA (K := K) (EXTERNAL_INITIAL.val[round.val]!) =
          R0P.poseidonExternalInitial ⟨round.val, h4⟩ := funext (ei_rows ⟨round.val, h4⟩)
      rw [e, ec]
      exact (ar_init ⟨round.val, hr⟩ h4 (liftA s)).symm
  · have hlt4 : ¬ round < 4#usize := by rw [UScalar.lt_equiv]; scalar_tac
    by_cases h18 : round.val < 18
    · have hlt18 : round < 18#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hsub : (Usize.wrapping_sub round 4#usize).val = round.val - 4 := by
        rw [usub _ _ (by rw [v4]; omega), v4]
      have hb : (Usize.wrapping_sub round 4#usize).val < (14#usize).val := by rw [hsub, v14]; omega
      obtain ⟨t, ht, htv⟩ := internal_round_lift (K := K) s
        (INTERNAL.val[(Usize.wrapping_sub round 4#usize).val]!) INTERNAL_SHIFTS
        internal_shifts_bound internal_shifts_ok
      refine ⟨t, ?_, ?_⟩
      · rw [apply_round, if_neg hlt4, if_pos hlt18]
        simp only [lift, bind_tc_ok, index_ok INTERNAL _ hb]
        exact ht
      · have e : liftA (K := K) t = _ := funext htv
        have ec : liftU (K := K) (INTERNAL.val[(Usize.wrapping_sub round 4#usize).val]!) =
            R0P.poseidonInternalConstants ⟨round.val - 4, by omega⟩ := by
          rw [hsub]; exact ic_all ⟨round.val - 4, by omega⟩
        rw [e, ec]
        exact (ar_int ⟨round.val, hr⟩ h4 (by show round.val < 4 + 14; omega) (liftA s)).symm
    · have hlt18 : ¬ round < 18#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hsub : (Usize.wrapping_sub round 18#usize).val = round.val - 4 - 14 := by
        rw [usub _ _ (by rw [v18]; omega), v18]; omega
      have hb : (Usize.wrapping_sub round 18#usize).val < (4#usize).val := by rw [hsub, v4]; omega
      obtain ⟨t, ht, htv⟩ := full_round_lift (K := K) s
        (EXTERNAL_FINAL.val[(Usize.wrapping_sub round 18#usize).val]!)
      refine ⟨t, ?_, ?_⟩
      · rw [apply_round, if_neg hlt4, if_neg hlt18]
        simp only [lift, bind_tc_ok, index_ok_gen EXTERNAL_FINAL _ hb]
        exact ht
      · have e : liftA (K := K) t = _ := funext htv
        have ec : liftA (K := K) (EXTERNAL_FINAL.val[(Usize.wrapping_sub round 18#usize).val]!) =
            R0P.poseidonExternalFinal ⟨round.val - 4 - 14, by omega⟩ := by
          rw [hsub]; exact funext (ef_rows ⟨round.val - 4 - 14, by omega⟩)
        rw [e, ec]
        exact (ar_fin ⟨round.val, hr⟩ h4 (by show ¬ round.val < 4 + 14; omega) (liftA s)).symm

/-! ### Leading pair -/

theorem absorb_loop (pre absorb : Array U32 16#usize) :
    ∀ (n : Nat) (i : Usize) (out : Array U32 16#usize), i.val + n = 8 →
      ∃ o, absorb_into_loop pre absorb out i = ok o ∧ ∀ k, k < 16 →
        (i.val ≤ k → k < 8 → liftU (K := K) (o.val[k]!) = liftU (pre.val[k]!) + liftU (absorb.val[k]!)) ∧
        (¬ (i.val ≤ k ∧ k < 8) → o.val[k]! = out.val[k]!)
  | 0, i, out, h => by
      refine ⟨out, ?_, fun k hk => ⟨fun h1 h2 => absurd h1 (by omega), fun _ => rfl⟩⟩
      rw [absorb_into_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, i, out, h => by
      have hlt : i < 8#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : i.val < (16#usize).val := by rw [v16]; omega
      have hi1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨z, hz, hzv⟩ := add_lift (K := K) (pre.val[i.val]!) (absorb.val[i.val]!)
      obtain ⟨o, ho, hov⟩ := absorb_loop pre absorb n (Usize.wrapping_add i 1#usize) (out.set i z)
        (by rw [hi1]; omega)
      refine ⟨o, ?_, fun k hk => ⟨fun hik hk8 => ?_, fun hn => ?_⟩⟩
      · rw [absorb_into_loop, if_pos hlt]
        simp only [lift, bind_tc_ok, index_ok pre i hb, index_ok absorb i hb, hz, update_ok out i z hb]
        exact ho
      · by_cases e : k = i.val
        · subst e
          rw [(hov i.val hk).2 (by rw [hi1]; omega), set_get' out i z hb i.val, if_pos rfl]
          exact hzv
        · exact (hov k hk).1 (by rw [hi1]; omega) hk8
      · rw [(hov k hk).2 (by rw [hi1]; omega), set_get' out i z hb k, if_neg (by omega)]

theorem leading_pair_lift (pre absorb c0 c1 : Array U32 16#usize)
    (h0 : ∀ i : Fin 16, liftU (K := K) (c0.val[i.val]!) = R0P.poseidonExternalInitial 0 i)
    (h1 : ∀ i : Fin 16, liftU (K := K) (c1.val[i.val]!) = R0P.poseidonExternalInitial 1 i) :
    ∃ t, leading_pair pre absorb c0 c1 = ok t ∧
      liftA (K := K) t = R0P.poseidonLeadingPair (liftA pre) (liftA absorb) := by
  obtain ⟨a, ha, hav⟩ := absorb_loop (K := K) pre absorb 8 0#usize pre (by rw [z0])
  obtain ⟨s, hs, hsv⟩ := external_lift (K := K) a
  obtain ⟨t1, ht1, ht1v⟩ := full_round_lift (K := K) s c0
  obtain ⟨t2, ht2, ht2v⟩ := full_round_lift (K := K) t1 c1
  refine ⟨t2, ?_, ?_⟩
  · rw [leading_pair]
    simp only [absorb_into, ha, bind_tc_ok, hs, ht1, ht2]
  · have ea : liftA (K := K) a =
        fun lane => if lane.val < 8 then liftA pre lane + liftA absorb lane else liftA pre lane := by
      funext lane
      by_cases hl : lane.val < 8
      · rw [if_pos hl]
        exact (hav lane.val lane.isLt).1 (z0.trans_le (Nat.zero_le _)) hl
      · rw [if_neg hl]
        show liftU (a.val[lane.val]!) = liftU (pre.val[lane.val]!)
        rw [(hav lane.val lane.isLt).2 (by rw [z0]; omega)]
    have es : liftA (K := K) s = _ := funext hsv
    have e1 : liftA (K := K) t1 = _ := funext ht1v
    have e2 : liftA (K := K) t2 = _ := funext ht2v
    have ec0 : liftA (K := K) c0 = R0P.poseidonExternalInitial 0 := funext h0
    have ec1 : liftA (K := K) c1 = R0P.poseidonExternalInitial 1 := funext h1
    rw [e2, e1, es, ea, ec0, ec1]
    rfl

/-! ### perm_rounds -/

theorem perm_loop (B : R0Z.BuilderModel.BlockIn K) :
    ∀ (n : Nat) (k : Usize) (rounds : Array (Array U32 16#usize) 11#usize) (state : Array U32 16#usize),
      k.val + n = 11 → 1 ≤ k.val →
      (∀ (r : Nat) (i : Fin 16), r < k.val →
        liftU (K := K) ((rounds.val[r]!).val[i.val]!) = R0Z.BuilderModel.blockIter B (r + 1) i) →
      liftA (K := K) state = R0Z.BuilderModel.blockIter B k.val →
      ∃ out, perm_rounds_loop rounds state k = ok out ∧ RoundsOk out B
  | 0, k, rounds, state, h, _, hinv, _ => by
      refine ⟨rounds, ?_, fun r i hr => hinv r i (by omega)⟩
      rw [perm_rounds_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, k, rounds, state, h, hk1, hinv, hst => by
      have hlt : k < 11#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hkb : k.val < (11#usize).val := by rw [v11]; omega
      have h2k : (Usize.wrapping_mul 2#usize k).val = 2 * k.val := by
        rw [umul _ _ (by rw [z2]; omega), z2]
      have h2k1 : (Usize.wrapping_add (Usize.wrapping_mul 2#usize k) 1#usize).val = 2 * k.val + 1 := by
        rw [uadd _ _ (by rw [h2k, z1]; omega), h2k, z1]
      have hkk : (Usize.wrapping_add k 1#usize).val = k.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨a, ha, hav⟩ := apply_round_lift (K := K) state (Usize.wrapping_mul 2#usize k)
        (by rw [h2k]; omega)
      obtain ⟨s1, hs1, hs1v⟩ := apply_round_lift (K := K) a
        (Usize.wrapping_add (Usize.wrapping_mul 2#usize k) 1#usize) (by rw [h2k1]; omega)
      have f1 : (⟨(Usize.wrapping_mul 2#usize k).val, by rw [h2k]; omega⟩ : Fin 22) =
          ⟨2 * k.val, by omega⟩ := Fin.ext h2k
      have f2 : (⟨(Usize.wrapping_add (Usize.wrapping_mul 2#usize k) 1#usize).val, by rw [h2k1]; omega⟩ :
          Fin 22) = ⟨2 * k.val + 1, by omega⟩ := Fin.ext h2k1
      have hnew : liftA (K := K) s1 = R0Z.BuilderModel.blockIter B (k.val + 1) := by
        rw [hs1v, hav, hst, iter_succ B k.val (by omega), trans_succ k.val _ (by omega), f1, f2]
      obtain ⟨o, ho, hR⟩ := perm_loop B n (Usize.wrapping_add k 1#usize) (rounds.set k s1) s1
        (by rw [hkk]; omega) (by rw [hkk]; omega)
        (fun r i hr => by
          rw [hkk] at hr
          rw [set_get_a rounds k s1 hkb r]
          by_cases e : r = k.val
          · rw [if_pos e, e]
            exact congrFun hnew i
          · rw [if_neg e]
            exact hinv r i (by omega))
        (by rw [hkk]; exact hnew)
      refine ⟨o, ?_, hR⟩
      rw [perm_rounds_loop, if_pos hlt]
      simp only [lift, bind_tc_ok, ha, hs1, update_ok_a rounds k s1 hkb]
      exact ho

/-- **RoundsOk for the copy.**  If the Rust pre-state and absorption lift to the
model block, the extracted copy's `perm_rounds` returns rounds satisfying
`RoundsOk` for that block. -/
theorem perm_rounds_lift (pre absorb : Array U32 16#usize) (B : R0Z.BuilderModel.BlockIn K)
    (he : EndsLift pre absorb B) :
    ∃ rounds, perm_rounds pre absorb = ok rounds ∧ RoundsOk rounds B := by
  have hb0 : (0#usize : Usize).val < (4#usize).val := by rw [z0, v4]; omega
  have hb1 : (1#usize : Usize).val < (4#usize).val := by rw [z1, v4]; omega
  have hb11 : (0#usize : Usize).val < (11#usize).val := by rw [z0, v11]; omega
  obtain ⟨st, hst, hstv⟩ := leading_pair_lift (K := K) pre absorb
    (EXTERNAL_INITIAL.val[(0#usize : Usize).val]!) (EXTERNAL_INITIAL.val[(1#usize : Usize).val]!)
    (fun i => by rw [z0]; exact ei_rows 0 i) (fun i => by rw [z1]; exact ei_rows 1 i)
  have hpre : liftA (K := K) pre = B.pre := funext he.pre
  have habs : liftA (K := K) absorb = B.absorb := funext he.absorb
  have h1 : liftA (K := K) st = R0Z.BuilderModel.blockIter B 1 := by
    show liftA st = R0Z.BuilderModel.blockIter B (0 + 1)
    rw [hstv, hpre, habs, iter_succ B 0 (by omega), iter_zero, trans_zero]
  obtain ⟨out, ho, hR⟩ := perm_loop (K := K) B 10 1#usize
    ((Array.repeat 11#usize (Array.repeat 16#usize 0#u32)).set 0#usize st) st
    (by rw [z1]) (le_of_eq z1.symm)
    (fun r i hr => by
      rw [z1] at hr
      obtain rfl : r = 0 := by omega
      rw [set_get_a _ 0#usize st hb11 0, z0, if_pos rfl]
      exact congrFun h1 i)
    (by rw [z1]; exact h1)
  refine ⟨out, ?_, hR⟩
  rw [perm_rounds]
  simp only [index_ok_gen EXTERNAL_INITIAL 0#usize hb0, index_ok_gen EXTERNAL_INITIAL 1#usize hb1,
    bind_tc_ok, hst, update_ok_a _ 0#usize st hb11]
  exact ho

end R0Z.PoseidonRefine

#print axioms R0Z.PoseidonRefine.apply_round_lift
#print axioms R0Z.PoseidonRefine.leading_pair_lift
#print axioms R0Z.PoseidonRefine.perm_rounds_lift
