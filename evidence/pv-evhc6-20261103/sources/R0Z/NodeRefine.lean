import R0Z.BlockRefine

/-! Node writer, sponge pieces and the relocation read-back (DESIGN-BUILDER-MODEL §10),
with wide M31 add/sub lemmas (canonical inputs below p, closing B3). -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result

/-! ### Wide M31 lemmas (inputs < p = 2^31 - 1) -/

theorem u32_add_small (a b : U32) (h : a.val + b.val < 2 ^ 32) : (U32.wrapping_add a b).val = a.val + b.val := by
  rw [U32.wrapping_add_val_eq]; exact Nat.mod_eq_of_lt (by rw [UScalar.size_def]; simpa using h)

theorem u32_sub_small (a b : U32) (h : b.val ≤ a.val) : (U32.wrapping_sub a b).val = a.val - b.val := by
  rw [U32.wrapping_sub_val_eq, UScalar.size_def]
  simp only [show UScalarTy.U32.numBits = 32 from rfl]
  have ha := a.hBounds
  rw [show a.val + (2 ^ 32 - b.val) = (a.val - b.val) + 2 ^ 32 by
    simp only [show UScalarTy.U32.numBits = 32 from rfl] at ha; omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by simp only [show UScalarTy.U32.numBits = 32 from rfl] at ha; omega)

theorem pval : (R0BlockCopies.P : U32).val = 2147483647 := by rw [R0BlockCopies.P]; simp
theorem tval : (R0BlockCopies.TWEAK : U32).val = 1095962629 := by rw [R0BlockCopies.TWEAK]; simp

theorem m31_add_spec (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ z, R0BlockCopies.m31_add a b = ok z ∧
      z.val = (if 2147483647 ≤ a.val + b.val then a.val + b.val - 2147483647 else a.val + b.val) := by
  have h1 := u32_add_small a b (by omega)
  rw [R0BlockCopies.m31_add]
  simp only [lift, bind_tc_ok]
  by_cases hs : U32.wrapping_add a b >= R0BlockCopies.P
  · rw [if_pos hs]
    have hs' : 2147483647 ≤ a.val + b.val := by rw [ge_iff_le, UScalar.le_equiv, pval, h1] at hs; exact hs
    exact ⟨_, rfl, by rw [u32_sub_small _ _ (by rw [pval, h1]; exact hs'), h1, pval, if_pos hs']⟩
  · rw [if_neg hs]
    have hs' : ¬ 2147483647 ≤ a.val + b.val := by rw [ge_iff_le, UScalar.le_equiv, pval, h1] at hs; exact hs
    exact ⟨_, rfl, by rw [h1, if_neg hs']⟩

theorem m31_sub_spec_wide (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    ∃ z, R0BlockCopies.m31_sub a b = ok z ∧
      z.val = (if b.val ≤ a.val then a.val - b.val else a.val + 2147483647 - b.val) := by
  have h1 := u32_add_small a R0BlockCopies.P (by rw [pval]; omega)
  rw [pval] at h1
  have h2 : (U32.wrapping_sub (U32.wrapping_add a R0BlockCopies.P) b).val = a.val + 2147483647 - b.val :=
    by rw [u32_sub_small _ _ (by rw [h1]; omega), h1]
  rw [R0BlockCopies.m31_sub]
  simp only [lift, bind_tc_ok]
  by_cases hs : U32.wrapping_sub (U32.wrapping_add a R0BlockCopies.P) b >= R0BlockCopies.P
  · rw [if_pos hs]
    have hs' : 2147483647 ≤ a.val + 2147483647 - b.val := by
      rw [ge_iff_le, UScalar.le_equiv, pval, h2] at hs; exact hs
    exact ⟨_, rfl, by rw [u32_sub_small _ _ (by rw [pval, h2]; exact hs'), h2, pval, if_pos (by omega)]; omega⟩
  · rw [if_neg hs]
    have hs' : ¬ 2147483647 ≤ a.val + 2147483647 - b.val := by
      rw [ge_iff_le, UScalar.le_equiv, pval, h2] at hs; exact hs
    exact ⟨_, rfl, by rw [h2, if_neg (by omega)]⟩

/-- B3 (a): the large-tweak read-back of the earlier copy, R0WriterCopies.node_right_lane7. -/
theorem node_right_lane7_spec (x : U32) (hx : x.val < 2147483647) :
    ∃ z, R0WriterCopies.node_right_lane7 x = ok z ∧
      z.val = (if 1095962629 ≤ x.val then x.val - 1095962629 else x.val + 2147483647 - 1095962629) := by
  have pv : (R0WriterCopies.P : U32).val = 2147483647 := by rw [R0WriterCopies.P]; simp
  have tv : (R0WriterCopies.TWEAK : U32).val = 1095962629 := by rw [R0WriterCopies.TWEAK]; simp
  have h1 := u32_add_small x R0WriterCopies.P (by rw [pv]; omega)
  rw [pv] at h1
  have h2 : (U32.wrapping_sub (U32.wrapping_add x R0WriterCopies.P) R0WriterCopies.TWEAK).val =
      x.val + 2147483647 - 1095962629 := by rw [u32_sub_small _ _ (by rw [h1, tv]; omega), h1, tv]
  rw [R0WriterCopies.node_right_lane7, R0WriterCopies.m31_sub]
  simp only [lift, bind_tc_ok]
  by_cases hs : U32.wrapping_sub (U32.wrapping_add x R0WriterCopies.P) R0WriterCopies.TWEAK >= R0WriterCopies.P
  · rw [if_pos hs]
    have hs' : 2147483647 ≤ x.val + 2147483647 - 1095962629 := by
      rw [ge_iff_le, UScalar.le_equiv, pv, h2] at hs; exact hs
    exact ⟨_, rfl, by rw [u32_sub_small _ _ (by rw [pv, h2]; exact hs'), h2, pv, if_pos (by omega)]; omega⟩
  · rw [if_neg hs]
    have hs' : ¬ 2147483647 ≤ x.val + 2147483647 - 1095962629 := by
      rw [ge_iff_le, UScalar.le_equiv, pv, h2] at hs; exact hs
    exact ⟨_, rfl, by rw [h2, if_neg (by omega)]⟩

variable {K : Type} [Field K]

theorem lift_m31_add [CharP K 0x7fffffff] (a b : Nat) :
    (((if 2147483647 ≤ a + b then a + b - 2147483647 else a + b : Nat)) : K) = (a : K) + (b : K) := by
  split_ifs with h
  · rw [Nat.cast_sub h, CharP.cast_eq_zero K 0x7fffffff, sub_zero, Nat.cast_add]
  · rw [Nat.cast_add]

theorem lift_m31_sub [CharP K 0x7fffffff] (a b : Nat) (hb : b < 2147483647) :
    (((if b ≤ a then a - b else a + 2147483647 - b : Nat)) : K) = (a : K) - (b : K) := by
  split_ifs with h
  · rw [Nat.cast_sub h]
  · rw [Nat.cast_sub (by omega), Nat.cast_add, CharP.cast_eq_zero K 0x7fffffff]; ring

/-- B3 (a), lifted: the read-back lane is the pre-state lane minus the tweak. -/
theorem node_right_lane7_lift [CharP K 0x7fffffff] (x : U32) (hx : x.val < 2147483647) :
    ∃ z, R0WriterCopies.node_right_lane7 x = ok z ∧
      liftU (K := K) z = liftU x - (0x4153_1005 : K) := by
  obtain ⟨z, hz, hv⟩ := node_right_lane7_spec x hx
  refine ⟨z, hz, ?_⟩
  unfold liftU
  rw [hv, lift_m31_sub _ _ (by norm_num)]
  norm_num

/-- add then subtract the tweak is the identity on canonical values. -/
theorem add_sub_tweak (r : Nat) (hr : r < 2147483647) :
    (let s := (if 2147483647 ≤ r + 1095962629 then r + 1095962629 - 2147483647 else r + 1095962629)
     if 1095962629 ≤ s then s - 1095962629 else s + 2147483647 - 1095962629) = r := by
  simp only []
  split_ifs <;> omega

/-! ### node_pre / node_absorb -/

theorem node_pre_loop_spec (right : Array U32 8#usize) :
    ∀ (n : Nat) (lane : Usize) (pre : Array U32 16#usize), lane.val + n = 8 →
      ∃ p', R0BlockCopies.node_pre_loop right pre lane = ok p' ∧
        ∀ k, p'.val[k]! = if 8 + lane.val ≤ k ∧ k < 16 then right.val[k - 8]! else pre.val[k]!
  | 0, lane, pre, h => by
      refine ⟨pre, ?_, fun k => by rw [if_neg (by omega)]⟩
      rw [R0BlockCopies.node_pre_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, lane, pre, h => by
      have hlt : lane < 8#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : lane.val < (8#usize).val := by simp; omega
      have h8 : (Usize.wrapping_add 8#usize lane).val = 8 + lane.val := by rw [uadd _ _ (by scalar_tac)]; simp
      have hb8 : (Usize.wrapping_add 8#usize lane).val < (16#usize).val := by rw [h8]; simp; omega
      have hl1 : (Usize.wrapping_add lane 1#usize).val = lane.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨p', hp', hs⟩ := node_pre_loop_spec right n (Usize.wrapping_add lane 1#usize)
        (pre.set (Usize.wrapping_add 8#usize lane) (right.val[lane.val]!)) (by rw [hl1]; omega)
      refine ⟨p', ?_, fun k => ?_⟩
      · rw [R0BlockCopies.node_pre_loop, if_pos hlt, index_ok right lane hb]
        simp only [bind_tc_ok, lift]
        rw [update_ok pre _ _ hb8]
        simp only [bind_tc_ok]
        exact hp'
      · have g := set_get' pre (Usize.wrapping_add 8#usize lane) (right.val[lane.val]!) hb8 k
        rw [h8] at g
        rw [hs k, hl1, g]
        split_ifs <;> first | rfl | omega | (rw [show k - 8 = lane.val by omega])

theorem rep16 (k : Nat) : (((Array.repeat 16#usize 0#u32 : Array U32 16#usize).val[k]! : U32)) = 0#u32 := by
  rw [Array.repeat_val]
  by_cases hk : k < (16#usize : Usize).val
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_pos hk]; rfl
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, if_neg hk]; rfl

theorem node_pre_spec (right : Array U32 8#usize) (hr : ∀ i, i < 8 → (right.val[i]!).val < 2147483647) :
    ∃ pre, R0BlockCopies.node_pre right = ok pre ∧
      ∀ k, (pre.val[k]!).val = if k < 8 then 0 else if k = 15 then
        (if 2147483647 ≤ (right.val[7]!).val + 1095962629 then (right.val[7]!).val + 1095962629 - 2147483647
         else (right.val[7]!).val + 1095962629)
        else if k < 16 then (right.val[k - 8]!).val else 0 := by
  obtain ⟨p1, hp1, hs1⟩ := node_pre_loop_spec right 8 0#usize (Array.repeat 16#usize 0#u32) (by simp)
  obtain ⟨z, hz, hzv⟩ := m31_add_spec (right.val[7]!) R0BlockCopies.TWEAK (hr 7 (by norm_num))
    (by rw [tval]; norm_num)
  rw [tval] at hzv
  have h15 : (15#usize : Usize).val < (16#usize).val := by simp
  refine ⟨p1.set 15#usize z, ?_, fun k => ?_⟩
  · rw [R0BlockCopies.node_pre, hp1]
    simp only [bind_tc_ok]
    rw [index_ok right 7#usize (by simp)]
    simp only [bind_tc_ok]
    rw [show (7#usize : Usize).val = 7 by simp, hz]
    simp only [bind_tc_ok]
    rw [update_ok p1 _ _ h15]
  · rw [set_get' p1 15#usize z h15 k, hs1 k, rep16, show (15#usize : Usize).val = 15 by simp]
    simp only [show (0#usize : Usize).val = 0 by simp, Nat.add_zero]
    have z0 : (0#u32 : U32).val = 0 := by simp
    by_cases e15 : k = 15
    · rw [if_pos e15, if_neg (by omega), if_pos e15, hzv]
    rw [if_neg e15]
    by_cases a : k < 8
    · rw [if_neg (show ¬ (8 ≤ k ∧ k < 16) by omega), if_pos a, z0]
    rw [if_neg a, if_neg e15]
    by_cases b : k < 16
    · rw [if_pos (show 8 ≤ k ∧ k < 16 by omega), if_pos b]
    · rw [if_neg (show ¬ (8 ≤ k ∧ k < 16) by omega), if_neg b, z0]

theorem node_absorb_loop_spec (left : Array U32 8#usize) :
    ∀ (n : Nat) (lane : Usize) (ab : Array U32 16#usize), lane.val + n = 8 →
      ∃ a', R0BlockCopies.node_absorb_loop left ab lane = ok a' ∧
        ∀ k, a'.val[k]! = if lane.val ≤ k ∧ k < 8 then left.val[k]! else ab.val[k]!
  | 0, lane, ab, h => by
      refine ⟨ab, ?_, fun k => by rw [if_neg (by omega)]⟩
      rw [R0BlockCopies.node_absorb_loop, if_neg (by rw [UScalar.lt_equiv]; scalar_tac)]
  | n + 1, lane, ab, h => by
      have hlt : lane < 8#usize := by rw [UScalar.lt_equiv]; scalar_tac
      have hb : lane.val < (8#usize).val := by simp; omega
      have hb16 : lane.val < (16#usize).val := by simp; omega
      have hl1 : (Usize.wrapping_add lane 1#usize).val = lane.val + 1 := uadd _ _ (by scalar_tac)
      obtain ⟨a', ha', hs⟩ := node_absorb_loop_spec left n (Usize.wrapping_add lane 1#usize)
        (ab.set lane (left.val[lane.val]!)) (by rw [hl1]; omega)
      refine ⟨a', ?_, fun k => ?_⟩
      · rw [R0BlockCopies.node_absorb_loop, if_pos hlt, index_ok left lane hb]
        simp only [bind_tc_ok]
        rw [update_ok ab _ _ hb16]
        simp only [bind_tc_ok, lift]
        exact ha'
      · rw [hs k, hl1, set_get' ab lane _ hb16 k]
        split_ifs <;> first | rfl | omega | (subst_vars; rfl)

theorem node_absorb_spec (left : Array U32 8#usize) :
    ∃ ab, R0BlockCopies.node_absorb left = ok ab ∧
      ∀ k, ab.val[k]! = if k < 8 then left.val[k]! else 0#u32 := by
  obtain ⟨a, ha, hs⟩ := node_absorb_loop_spec left 8 0#usize (Array.repeat 16#usize 0#u32) (by simp)
  refine ⟨a, by rw [R0BlockCopies.node_absorb]; exact ha, fun k => ?_⟩
  rw [hs k, rep16]
  simp only [show (0#usize : Usize).val = 0 by simp, Nat.zero_le, true_and]

/-! ### The node block against the model -/

/-- The Rust digests lift to the model's children. -/
def DigestLift (d : Array U32 8#usize) (D : R0P.Digest K) : Prop :=
  ∀ i : Fin 8, liftU (K := K) (d.val[i.val]!) = D i

theorem node_ends_lift [CharP K 0x7fffffff] (left right : Array U32 8#usize) (L R : R0P.Digest K)
    (hl : DigestLift left L) (hr : DigestLift right R)
    (hc : ∀ i, i < 8 → (right.val[i]!).val < 2147483647) :
    ∃ pre ab, R0BlockCopies.node_pre right = ok pre ∧ R0BlockCopies.node_absorb left = ok ab ∧
      EndsLift pre ab (R0Z.BuilderModel.nodeIn L R) := by
  obtain ⟨pre, hp, hps⟩ := node_pre_spec right hc
  obtain ⟨ab, ha, has⟩ := node_absorb_spec left
  refine ⟨pre, ab, hp, ha, ⟨fun i => ?_, fun i => ?_⟩⟩
  · have hi := i.isLt
    show liftU (pre.val[i.val]!) = (if i.val < 8 then 0 else if i.val = 15 then R 7 + (0x4153_1005 : K)
      else R ⟨i.val - 8, by omega⟩)
    unfold liftU
    rw [hps]
    by_cases a : i.val < 8
    · rw [if_pos a, if_pos a]; simp
    rw [if_neg a, if_neg a]
    by_cases b : i.val = 15
    · rw [if_pos b, if_pos b, lift_m31_add, ← hr 7]
      unfold liftU; norm_num
    rw [if_neg b, if_neg b, if_pos hi]
    exact hr ⟨i.val - 8, by omega⟩
  · show liftU (ab.val[i.val]!) = R0Z.BuilderModel.lo8 L i
    unfold R0Z.BuilderModel.lo8
    rw [has]
    by_cases a : i.val < 8
    · rw [if_pos a, dif_pos a]; exact hl ⟨i.val, a⟩
    · rw [if_neg a, dif_neg a]; unfold liftU; simp

/-- The extracted node writer equals the model's node block, every cell,
relative to the Poseidon plug-in `RoundsOk`. -/
theorem node_model [CharP K 0x7fffffff] (left right : Array U32 8#usize)
    (rounds : Array (Array U32 16#usize) 11#usize) (L R : R0P.Digest K)
    (hl : DigestLift left L) (hr : DigestLift right R)
    (hc : ∀ i, i < 8 → (right.val[i]!).val < 2147483647)
    (hround : RoundsOk rounds (R0Z.BuilderModel.nodeIn L R)) :
    ∃ b, R0BlockCopies.write_node left right rounds = ok b ∧
      ∀ (l c : Fin 16), liftU (K := K) (b.val[l.val * 16 + c.val]!) =
        R0Z.BuilderModel.blockCell (R0Z.BuilderModel.nodeIn L R) l.val c := by
  obtain ⟨pre, ab, hp, ha, he⟩ := node_ends_lift left right L R hl hr hc
  obtain ⟨b, hb, hs⟩ := block_model pre ab rounds _ he hround
  refine ⟨b, ?_, hs⟩
  rw [R0BlockCopies.write_node, hp]
  simp only [bind_tc_ok]
  rw [ha]
  simp only [bind_tc_ok]
  exact hb

#print axioms m31_add_spec
#print axioms m31_sub_spec_wide
#print axioms node_right_lane7_spec
#print axioms node_right_lane7_lift
#print axioms add_sub_tweak
#print axioms node_pre_spec
#print axioms node_absorb_spec
#print axioms node_ends_lift
#print axioms node_model
end R0Z.WriterRefine
