import R0Z.PoseidonRounds

/-! Canonical outputs of the Poseidon copy (DESIGN-BUILDER-MODEL §12 (2)).

Every lane the copy's `perm_rounds` writes is below p: each is a
`cast (x % p)` (m31_add, internal lanes) of a u64 expression.  This is what
lets a computed digest be the right child of a node (node_pre adds the tweak to
lane 7 with a conditional subtraction).  Field-free: no K. -/
set_option autoImplicit false

namespace R0Z.PoseidonRefine
open Aeneas Aeneas.Std Result R0PoseidonCopy R0Z.WriterRefine

theorem bind_ok_inv {α β : Type} {x : Result α} {f : α → Result β} {t : β}
    (h : (do let a ← x; f a) = ok t) : ∃ a, x = ok a ∧ f a = ok t := by
  cases x with
  | ok a => exact ⟨a, rfl, by simpa using h⟩
  | fail e => simp at h
  | div => simp at h

/-- All sixteen lanes below p. -/
def Canon (t : Array U32 16#usize) : Prop := ∀ k, k < 16 → (t.val[k]!).val < 2147483647

theorem add_canon (a b : U32) : ∃ z, m31_add a b = ok z ∧ z.val < 2147483647 := by
  rw [m31_add]
  simp only [lift, bind_tc_ok, remP]
  exact ⟨_, rfl, canon_mod _⟩

theorem add_loop_canon (gr : Array U32 16#usize) (sums : Array U32 4#usize) :
    ∀ (n : Nat) (i : Usize) (out : Array U32 16#usize), i.val + n = 16 →
      (∀ k, k < i.val → (out.val[k]!).val < 2147483647) →
      ∀ o, ext_add_loop gr sums out i = ok o → Canon o
  | 0, i, out, h, hout, o, ho => by
      rw [ext_add_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)] at ho
      injection ho with e
      subst e
      exact fun k hk => hout k (by omega)
  | n + 1, i, out, h, hout, o, ho => by
      have hlt : i < 16#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : i.val < (16#usize).val := by rw [v16]; omega
      have hi1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      have hrb : (⟨BitVec.umod i.bv (4#usize : Usize).bv⟩ : Usize).val < (4#usize).val := by
        rw [umod_val, v4]; omega
      obtain ⟨z, hz, hzc⟩ := add_canon (gr.val[i.val]!)
        (sums.val[(⟨BitVec.umod i.bv (4#usize : Usize).bv⟩ : Usize).val]!)
      rw [ext_add_loop, if_pos hlt] at ho
      simp only [lift, bind_tc_ok, index_ok gr i hb, rem_ok i 4#usize (by rw [v4]; omega),
        index_ok sums _ hrb, hz, update_ok out i z hb] at ho
      refine add_loop_canon gr sums n _ _ (by rw [hi1]; omega) (fun k hk => ?_) o ho
      rw [hi1] at hk
      rw [set_get' out i z hb k]
      by_cases e : k = i.val
      · rw [if_pos e]; exact hzc
      · rw [if_neg e]; exact hout k (by omega)

theorem external_canon (s t : Array U32 16#usize) (h : external_linear s = ok t) : Canon t := by
  rw [external_linear] at h
  obtain ⟨gr, -, h⟩ := bind_ok_inv h
  obtain ⟨sm, -, h⟩ := bind_ok_inv h
  rw [ext_add] at h
  exact add_loop_canon gr sm 16 0#usize _ (by rw [z0]) (fun k hk => by rw [z0] at hk; omega) t h

theorem full_canon (s c t : Array U32 16#usize) (h : full_round s c = ok t) : Canon t := by
  rw [full_round] at h
  obtain ⟨a, -, h⟩ := bind_ok_inv h
  exact external_canon a t h

theorem lin_loop_canon (s : Array U32 16#usize) (shifts : Array U32 15#usize) (full : U32) :
    ∀ (n : Nat) (i : Usize) (out : Array U32 16#usize), i.val + n = 16 → 1 ≤ i.val →
      (∀ k, k < i.val → (out.val[k]!).val < 2147483647) →
      ∀ o, internal_linear_loop s shifts full out i = ok o → Canon o
  | 0, i, out, h, _, hout, o, ho => by
      rw [internal_linear_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)] at ho
      injection ho with e
      subst e
      exact fun k hk => hout k (by omega)
  | n + 1, i, out, h, h1, hout, o, ho => by
      have hlt : i < 16#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : i.val < (16#usize).val := by rw [v16]; omega
      have hi1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      have hsub : (Usize.wrapping_sub i 1#usize).val = i.val - 1 := by
        rw [usub _ _ (by rw [z1]; omega), z1]
      have hsb' : (Usize.wrapping_sub i 1#usize).val < (15#usize).val := by rw [hsub, v15]; omega
      rw [internal_linear_loop, if_pos hlt] at ho
      simp only [lift, bind_tc_ok, index_ok s i hb, index_ok shifts _ hsb', remP,
        update_ok out i _ hb] at ho
      refine lin_loop_canon s shifts full n _ _ (by rw [hi1]; omega) (by rw [hi1]; omega) ?_ o ho
      intro k hk
      rw [hi1] at hk
      rw [set_get' out i _ hb k]
      by_cases e : k = i.val
      · rw [if_pos e]; exact canon_mod _
      · rw [if_neg e]; exact hout k (by omega)

theorem internal_linear_canon (s : Array U32 16#usize) (shifts : Array U32 15#usize) (t : Array U32 16#usize)
    (h : internal_linear s shifts = ok t) : Canon t := by
  have hb0 : (0#usize : Usize).val < (16#usize).val := by rw [z0, v16]; omega
  rw [internal_linear] at h
  obtain ⟨part, -, h⟩ := bind_ok_inv h
  rw [index_ok s 0#usize hb0] at h
  simp only [bind_tc_ok] at h
  obtain ⟨full, -, h⟩ := bind_ok_inv h
  simp only [lift, bind_tc_ok, remP, update_ok _ 0#usize _ hb0] at h
  refine lin_loop_canon s shifts full 15 1#usize _ (by rw [z1]) (le_of_eq z1.symm) ?_ t h
  intro k hk
  rw [z1] at hk
  obtain rfl : k = 0 := by omega
  rw [set_get' _ 0#usize _ hb0 0, z0, if_pos rfl]
  exact canon_mod _

theorem internal_round_canon (s : Array U32 16#usize) (c0 : U32) (shifts : Array U32 15#usize)
    (t : Array U32 16#usize) (h : internal_round s c0 shifts = ok t) : Canon t := by
  have hb0 : (0#usize : Usize).val < (16#usize).val := by rw [z0, v16]; omega
  rw [internal_round, index_ok s 0#usize hb0] at h
  simp only [bind_tc_ok] at h
  obtain ⟨z, -, h⟩ := bind_ok_inv h
  obtain ⟨y, -, h⟩ := bind_ok_inv h
  rw [update_ok s 0#usize y hb0] at h
  simp only [bind_tc_ok] at h
  exact internal_linear_canon _ _ _ h

theorem apply_round_canon (s : Array U32 16#usize) (round : Usize) (t : Array U32 16#usize)
    (h : apply_round s round = ok t) : Canon t := by
  rw [apply_round] at h
  split_ifs at h
  · obtain ⟨a, -, h⟩ := bind_ok_inv h
    exact full_canon _ _ _ h
  · simp only [lift, bind_tc_ok] at h
    obtain ⟨c, -, h⟩ := bind_ok_inv h
    exact internal_round_canon _ _ _ _ h
  · simp only [lift, bind_tc_ok] at h
    obtain ⟨c, -, h⟩ := bind_ok_inv h
    exact full_canon _ _ _ h

theorem leading_canon (pre absorb c0 c1 t : Array U32 16#usize) (h : leading_pair pre absorb c0 c1 = ok t) :
    Canon t := by
  rw [leading_pair] at h
  obtain ⟨a, -, h⟩ := bind_ok_inv h
  obtain ⟨s, -, h⟩ := bind_ok_inv h
  obtain ⟨a1, -, h⟩ := bind_ok_inv h
  exact full_canon _ _ _ h

theorem perm_loop_canon :
    ∀ (n : Nat) (k : Usize) (rounds : Array (Array U32 16#usize) 11#usize) (state : Array U32 16#usize),
      k.val + n = 11 → (∀ r, r < k.val → Canon (rounds.val[r]!)) →
      ∀ out, perm_rounds_loop rounds state k = ok out → ∀ r, r < 11 → Canon (out.val[r]!)
  | 0, k, rounds, state, h, hinv, out, ho => by
      rw [perm_rounds_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)] at ho
      injection ho with e
      subst e
      exact fun r hr => hinv r (by omega)
  | n + 1, k, rounds, state, h, hinv, out, ho => by
      have hlt : k < 11#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hkb : k.val < (11#usize).val := by rw [v11]; omega
      have hkk : (Usize.wrapping_add k 1#usize).val = k.val + 1 := uadd _ _ (by scalar_tac)
      rw [perm_rounds_loop, if_pos hlt] at ho
      simp only [lift, bind_tc_ok] at ho
      obtain ⟨a, -, ho⟩ := bind_ok_inv ho
      obtain ⟨s1, hs1, ho⟩ := bind_ok_inv ho
      rw [update_ok_a rounds k s1 hkb] at ho
      simp only [bind_tc_ok] at ho
      refine perm_loop_canon n _ _ _ (by rw [hkk]; omega) (fun r hr => ?_) out ho
      rw [hkk] at hr
      rw [set_get_a rounds k s1 hkb r]
      by_cases e : r = k.val
      · rw [if_pos e]; exact apply_round_canon _ _ _ hs1
      · rw [if_neg e]; exact hinv r (by omega)

/-- Every row of the copy's perm_rounds output is canonical. -/
theorem perm_canon (pre absorb : Array U32 16#usize) (rounds : Array (Array U32 16#usize) 11#usize)
    (h : perm_rounds pre absorb = ok rounds) : ∀ r, r < 11 → Canon (rounds.val[r]!) := by
  have hb0 : (0#usize : Usize).val < (4#usize).val := by rw [z0, v4]; omega
  have hb1 : (1#usize : Usize).val < (4#usize).val := by rw [z1, v4]; omega
  have hb11 : (0#usize : Usize).val < (11#usize).val := by rw [z0, v11]; omega
  rw [perm_rounds] at h
  simp only [index_ok_gen EXTERNAL_INITIAL 0#usize hb0, index_ok_gen EXTERNAL_INITIAL 1#usize hb1,
    bind_tc_ok] at h
  obtain ⟨st, hst, h⟩ := bind_ok_inv h
  rw [update_ok_a _ 0#usize st hb11] at h
  simp only [bind_tc_ok] at h
  refine perm_loop_canon 10 1#usize _ st (by rw [z1]) (fun r hr => ?_) rounds h
  rw [z1] at hr
  obtain rfl : r = 0 := by omega
  rw [set_get_a _ 0#usize st hb11 0, z0, if_pos rfl]
  exact leading_canon _ _ _ _ _ hst

end R0Z.PoseidonRefine

#print axioms R0Z.PoseidonRefine.bind_ok_inv
#print axioms R0Z.PoseidonRefine.apply_round_canon
#print axioms R0Z.PoseidonRefine.perm_canon
