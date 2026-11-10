import NPH_R22Loops
import RPz7_S2K_DigestTotal
import AspisR1EbyKFinish.Funs
import T2Nat_RawBounds

/-! NPH_ (R22 item 2, batch 1: the OPEN non-field loop and decoder bodies, by the pattern of their
checked operations). Each lemma is about the existing gate definition; nothing merged is changed.
- PRECONDITION_B (reached-domain loop invariant): TerminalDecoder encode_digest_canonical_loop.body.
  Domain: iter = DigestTotal.cursor rows k with k ≤ 8. `enc_body_reached`: the body is ok on the
  domain (DigestTotal.body_word for k < 8, the exhausted iterator for k = 8). `enc_step_domain`: a
  cont step stays in the domain. `enc_entry` (rfl): the only caller encode_digest_canonical enters at
  cursor rows 0. So every body execution reached from the caller is ok (also DigestTotal.total).
- DIRECT, constant arithmetic: `late_public_const` (32 + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES = 832), the
  only checked op of encode_pool_v1_pair_late_public_statement_v1 and of
  decode_pool_v1_pair_late_public_statement_boxed_v1.
- DIRECT, shift by a constant below the width: `shr31i` (`x >>> 31#i32` on u64 is ok for every x), the
  only checked ops of AspisR1DotPushLocal.canonical.Dot.push (its rawFn is a callback: the Q.raw
  copies, TOTAL by NPH_R22QRawTotal).
- TOTAL: `ebyk_reduce_total` (AspisR1EbyKFinish.canonical.reduce is ok for every u64).
- DIRECT, guarded decrement: `usize_pred_ok`/`u32_pred_ok`/`u8_pred_ok` (x ≠ 0 → x - 1 ok) for
  MultiproofSortRef insert_step (guard at1 = 0), MultiproofConeRef levels (height = 0) and
  Op4P opening_rows (remaining = 0); `usize_pos_pred_ok` (i > 0 → i - 1 ok) and
  NPH_R22Loops.usize_succ_ok (¬ i >= n → i + 1 ok) for MultiproofConeRef valid_indices.
- DIRECT, cursor add followed by the bounds-checked range read [p, end): `cursor_direct`. If the
  wrapping program's range read at the wrapped end p.wrapping_add n succeeds, the checked p + n is
  ok with the same value (T2Nat_RawBounds.range_success and no_wrap). If that read fails, both
  profiles fail (bounds checks are on in both). Bodies: NCX_Reference read32 (p + 32), word (p + 8)
  and NJC_ReaderEmission Reader.raw (at + N). Standard axioms. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Loops4
open Aeneas Aeneas.Std Result ControlFlow AspisR1.NPH_R22FieldRef

/-! ### PRECONDITION_B: TerminalDecoder encode_digest_canonical_loop.body -/

theorem enc_stopped (rows : AspisR1.S2K.DigestTotal.Digest) (out : Array U8 32#usize) :
    AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical_loop.body
      (AspisR1.S2K.DigestTotal.cursor rows 8#usize) out = ok (done out) := by
  change AspisR1.S2K.DigestTotal.body _ _ = _
  simp only [AspisR1.S2K.DigestTotal.body, AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical_loop.body,
    AspisR1.S2K.DigestTotal.exhausted rows, bind_tc_ok]
  rfl

theorem enc_body_reached (rows : AspisR1.S2K.DigestTotal.Digest) (k : Usize) (hk : k.val ≤ 8)
    (out : Array U8 32#usize) :
    ∃ r, AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical_loop.body
      (AspisR1.S2K.DigestTotal.cursor rows k) out = ok r := by
  by_cases more : k.val < 8
  · exact ⟨_, AspisR1.S2K.DigestTotal.body_word rows k more out⟩
  · have eqk : k = 8#usize := by scalar_tac
    subst eqk
    exact ⟨_, enc_stopped rows out⟩

theorem enc_step_domain (rows : AspisR1.S2K.DigestTotal.Digest) (k : Usize) (hk : k.val ≤ 8)
    (out : Array U8 32#usize) (it : AspisR1.S2K.DigestTotal.Iter) (o : Array U8 32#usize)
    (h : AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical_loop.body
      (AspisR1.S2K.DigestTotal.cursor rows k) out = ok (cont (it, o))) :
    ∃ k' : Usize, k'.val ≤ 8 ∧ it = AspisR1.S2K.DigestTotal.cursor rows k' := by
  by_cases more : k.val < 8
  · rw [AspisR1.S2K.DigestTotal.body_word rows k more out] at h
    simp only [Result.ok.injEq, ControlFlow.cont.injEq, Prod.mk.injEq] at h
    exact ⟨Usize.ofNatCore (k.val+1) (by scalar_tac), by change k.val+1 ≤ 8; omega, h.1.symm⟩
  · have eqk : k = 8#usize := by scalar_tac
    subst eqk
    rw [enc_stopped rows out] at h
    cases h

theorem enc_entry (rows : AspisR1.S2K.DigestTotal.Digest) :
    AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical rows =
      AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical_loop
        (AspisR1.S2K.DigestTotal.cursor rows 0#usize) (Array.repeat 32#usize 0#u8) := by
  rfl

/-! ### DIRECT: constant arithmetic -/

theorem late_public_const :
    ∃ z, (32#usize + AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES :
      Result Usize) = ok z := by
  have hv : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES.val = 800 := by
    first
    | (unfold AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES; rfl)
    | (with_unfolding_all rfl)
    | (simp [AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES])
  have h32 : (32#usize : Usize).val = 32 := by first | rfl | simp
  have hb := AspisR1.NPH_R22QRawShift.numBits_ge
  have hpow : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) hb
  have hmax : (32#usize : Usize).val +
      AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES.val ≤ UScalar.max .Usize := by
    rw [h32, hv]
    first
    | (simp only [UScalar.max, UScalarTy.numBits]; omega)
    | (unfold UScalar.max; simp only [UScalarTy.numBits]; omega)
    | scalar_tac
  obtain ⟨z, hz, _⟩ := add_ok _ _ hmax
  exact ⟨z, hz⟩

/-! ### DIRECT: u64 shift by 31 (Dot.push) and TOTAL: EbyKFinish reduce -/

theorem shr31i (x : U64) : ∃ z, (x >>> 31#i32 : Result U64) = ok z ∧ z.val = x.val / 2147483648 := by
  have hb : (31#i32).val < UScalarTy.U64.numBits := by norm_num [UScalar.ofNatCore_val_eq]
  have hn : 0 ≤ (31#i32).val := by norm_num
  obtain ⟨z, hz, hv⟩ := WP.spec_imp_exists (UScalar.ShiftRight_IScalar_spec x (31#i32) hn hb)
  have hshiftNat : (31#i32).toNat = 31 := by rfl
  refine ⟨z, hz, ?_⟩
  rw [hv.1, hshiftNat, Nat.shiftRight_eq_div_pow]

theorem ebykP_val :
    (core.convert.num.FromU64U32.from AspisR1EbyKFinish.canonical.P).val = 2147483647 := by
  have hp : AspisR1EbyKFinish.canonical.P.val = 2147483647 := by
    norm_num [AspisR1EbyKFinish.canonical.P, UScalar.ofNatCore_val_eq]
  change (UScalar.cast .U64 AspisR1EbyKFinish.canonical.P).val = _
  rw [UScalar.cast_val_eq, hp]
  exact Nat.mod_eq_of_lt (by norm_num)

theorem ebyk_and_le (x : U64) :
    (x &&& core.convert.num.FromU64U32.from AspisR1EbyKFinish.canonical.P).val ≤ 2147483647 := by
  rw [UScalar.val_and, ebykP_val]
  exact Nat.and_le_right

/-- TOTAL: AspisR1EbyKFinish.canonical.reduce is ok for every u64. -/
theorem ebyk_reduce_total (x : U64) : ∃ y, AspisR1EbyKFinish.canonical.reduce x = ok y := by
  have hx : x.val < 18446744073709551616 := x.bv.isLt
  obtain ⟨i2, h2, v2⟩ := shr31i x
  have a1 := ebyk_and_le x
  have b1 : (x &&& core.convert.num.FromU64U32.from AspisR1EbyKFinish.canonical.P).val + i2.val ≤
      UScalar.max .U64 := by rw [v2, max64]; omega
  obtain ⟨x1, h3, v3⟩ := add_ok _ _ b1
  obtain ⟨i5, h5, v5⟩ := shr31i x1
  have a4 := ebyk_and_le x1
  have x1b : x1.val < 17179869184 := by rw [v3, v2]; omega
  have b2 : (x1 &&& core.convert.num.FromU64U32.from AspisR1EbyKFinish.canonical.P).val + i5.val ≤
      UScalar.max .U64 := by rw [v5, max64]; omega
  obtain ⟨x2, h6, v6⟩ := add_ok _ _ b2
  by_cases hge : x2 ≥ core.convert.num.FromU64U32.from AspisR1EbyKFinish.canonical.P
  · have hle : (core.convert.num.FromU64U32.from AspisR1EbyKFinish.canonical.P).val ≤ x2.val := by
      first | exact hge | scalar_tac
    obtain ⟨y, hy, _⟩ := sub_ok x2 _ hle
    exact ⟨_, by simp only [AspisR1EbyKFinish.canonical.reduce, lift, bind_tc_ok, h2, h3, h5, h6,
      if_pos hge, hy]⟩
  · exact ⟨_, by simp only [AspisR1EbyKFinish.canonical.reduce, lift, bind_tc_ok, h2, h3, h5, h6,
      if_neg hge]⟩

/-! ### DIRECT: guarded decrements and increments -/

theorem usize_pred_ok (x : Usize) (h : ¬ x = 0#usize) : ∃ z, (x - 1#usize : Result Usize) = ok z := by
  have h1 : (1#usize : Usize).val ≤ x.val := by scalar_tac
  obtain ⟨z, hz, _⟩ := sub_ok x 1#usize h1
  exact ⟨z, hz⟩

theorem usize_pos_pred_ok (x : Usize) (h : x > 0#usize) : ∃ z, (x - 1#usize : Result Usize) = ok z := by
  have h1 : (1#usize : Usize).val ≤ x.val := by scalar_tac
  obtain ⟨z, hz, _⟩ := sub_ok x 1#usize h1
  exact ⟨z, hz⟩

theorem u32_pred_ok (x : U32) (h : ¬ x = 0#u32) : ∃ z, (x - 1#u32 : Result U32) = ok z := by
  have h1 : (1#u32 : U32).val ≤ x.val := by scalar_tac
  obtain ⟨z, hz, _⟩ := sub_ok x 1#u32 h1
  exact ⟨z, hz⟩

theorem u8_pred_ok (x : U8) (h : ¬ x = 0#u8) : ∃ z, (x - 1#u8 : Result U8) = ok z := by
  have h1 : (1#u8 : U8).val ≤ x.val := by scalar_tac
  obtain ⟨z, hz, _⟩ := sub_ok x 1#u8 h1
  exact ⟨z, hz⟩

/-- valid_indices: `i + 1` on the else branch of `i >= n`. -/
theorem valid_indices_succ_ok (i n : Usize) (h : ¬ i >= n) :
    ∃ z, (i + 1#usize : Result Usize) = ok z ∧ z.val = i.val + 1 :=
  AspisR1.NPH_R22Loops.usize_succ_ok i n (by scalar_tac)

/-! ### DIRECT: cursor add followed by the bounds-checked range read -/

/-- If the range read [p, p.wrapping_add n) of b succeeds (the wrapping program's next step), the
checked p + n is ok with the same value. -/
theorem cursor_direct (b : Slice U8) (p n : Usize) (s : Slice U8)
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) b
      { start := p, «end» := Usize.wrapping_add p n } = ok s) :
    ∃ z, (p + n : Result Usize) = ok z ∧ z.val = (Usize.wrapping_add p n).val := by
  have hr := AspisR1.T2Nat_RawBounds.range_success b s p _ h
  have hw := AspisR1.T2Nat_RawBounds.no_wrap p n hr.1
  have hl : b.val.length ≤ UScalar.max .Usize := by
    first | exact b.property | (have := b.property; scalar_tac) | simpa using b.property
  have hsum : p.val + n.val ≤ UScalar.max .Usize := by
    have := hr.2; rw [hw] at this; omega
  obtain ⟨z, hz, hv⟩ := add_ok p n hsum
  exact ⟨z, hz, by rw [hv, hw]⟩

#print axioms enc_stopped
#print axioms enc_body_reached
#print axioms enc_step_domain
#print axioms enc_entry
#print axioms late_public_const
#print axioms shr31i
#print axioms ebykP_val
#print axioms ebyk_and_le
#print axioms ebyk_reduce_total
#print axioms usize_pred_ok
#print axioms usize_pos_pred_ok
#print axioms u32_pred_ok
#print axioms u8_pred_ok
#print axioms valid_indices_succ_ok
#print axioms cursor_direct
end AspisR1.NPH_R22Loops4
