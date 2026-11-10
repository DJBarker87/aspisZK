import NPH_R22CM31

/-! NPS_ (R22, last open definition, 2026-11-10, local): AspisR72Sampler.field.r24_canonical_mul
is TOTAL (a): the checked body returns `ok` for EVERY pair of QM31 inputs. The eight `≥ P`
guards return `ok none` (not a failure). In the remaining branch the checked sites are:
- sixteen u64 products `cast x * cast y` of widened u32 limbs: each ≤ (2^32-1)^2 < 2^64
  (`limb_mul_ok`; no canonicality needed);
- `PP = cast P * cast P` (`PP_ok`, value P*P < 2^62);
- the closure call (mask, checked shift `>>> 31#i32`, wrapping add): ok for every t, output
  < 2^34 (`closure_ok`; checked totality was NPH_R22CM31.R72_r24_closure_total);
- `2 * u`, `2 * v` (closure outputs < 2^34), `2 * PP` (< 2^63) (`two_mul_ok`);
- `3 * from P` (`three_P_ok`);
- `M31.reduce_u64`, TOTAL on every U64 (`reduce_ok`, from NPH_R22CM31.R72_reduce_wrapper and
  NPH_R22FieldRef.refReduce_total).
Every addition and subtraction in the body is an explicit `wrapping_*` call, which cannot fail.
`CM31.new` is `ok`. Statement form as NPH_R22QRawTotal.unified_total. Standard axioms. -/
set_option autoImplicit false
namespace AspisR1.NPS_R24Total
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef AspisR1.NPH_R22FieldCopies AspisR1.NPH_R22CM31

/-- Sequencing: a successful step whose continuation succeeds under the step's postcondition. -/
theorem step {α β : Type} {m : Result α} {f : α → Result β} {Q : α → Prop}
    (hm : ∃ x, m = ok x ∧ Q x) (hf : ∀ x, Q x → ∃ r, f x = ok r) :
    ∃ r, (m >>= f) = ok r := by
  obtain ⟨x, hx, hq⟩ := hm
  obtain ⟨r, hr⟩ := hf x hq
  exact ⟨r, by rw [hx]; exact hr⟩

theorem P_val : AspisR72Sampler.field.P.val = 2147483647 := by
  unfold AspisR72Sampler.field.P; rfl

/-- Site class 1: product of two widened u32 limbs (sixteen sites). -/
theorem limb_mul_ok (x y : U32) :
    ∃ z, (UScalar.cast .U64 x * UScalar.cast .U64 y : Result U64) = ok z ∧ True := by
  have hx : x.val < 4294967296 := x.bv.isLt
  have hy : y.val < 4294967296 := y.bv.isLt
  have hm : x.val * y.val ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨z, hz, _⟩ := mul_ok (UScalar.cast .U64 x) (UScalar.cast .U64 y)
    (by rw [cast64_val, cast64_val, max64]; omega)
  exact ⟨z, hz, trivial⟩

/-- Site 2: the PP constant. -/
theorem PP_ok :
    ∃ pp, AspisR72Sampler.field.r24_canonical_mul.PP = ok pp ∧ pp.val < 2^62 := by
  obtain ⟨z, hz, hv⟩ := mul_ok (UScalar.cast .U64 AspisR72Sampler.field.P)
    (UScalar.cast .U64 AspisR72Sampler.field.P) (by rw [cast64_val, P_val, max64]; omega)
  refine ⟨z, ?_, ?_⟩
  · unfold AspisR72Sampler.field.r24_canonical_mul.PP
    simp only [lift, bind_tc_ok]
    exact hz
  · rw [hv, cast64_val, P_val]; omega

/-- PP is TOTAL (no inputs). -/
theorem PP_total : ∃ pp, AspisR72Sampler.field.r24_canonical_mul.PP = ok pp := by
  obtain ⟨pp, h, _⟩ := PP_ok
  exact ⟨pp, h⟩

/-- Site 3: the closure call, ok for every argument, output below 2^34. -/
theorem closure_ok (c : AspisR72Sampler.field.r24_canonical_mul.closure) (t : U64) :
    ∃ u, AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call c t
      = ok u ∧ u.val < 2^34 := by
  obtain ⟨i2, h2, v2⟩ := shr31i_val t
  have ht : t.val < 18446744073709551616 := t.bv.isLt
  refine ⟨core.num.U64.wrapping_add (t &&& core.convert.num.FromU64U32.from AspisR72Sampler.field.P) i2,
    ?_, ?_⟩
  · simp only [AspisR72Sampler.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call,
      lift, bind_tc_ok, h2]
  · rw [core.num.U64.wrapping_add_val_eq]
    have h1 : (t &&& core.convert.num.FromU64U32.from AspisR72Sampler.field.P).val ≤ 2147483647 := by
      rw [UScalar.val_and, from_val, P_val]; exact Nat.and_le_right
    have hle := Nat.mod_le
      ((t &&& core.convert.num.FromU64U32.from AspisR72Sampler.field.P).val + i2.val) (UScalar.size .U64)
    omega

/-- Site class 4: doubling a value below 2^63 (2*u, 2*v, 2*PP). -/
theorem two_mul_ok (u : U64) (hu : u.val < 2^63) :
    ∃ z, (2#u64 * u : Result U64) = ok z ∧ True := by
  have h2 : (2#u64 : U64).val = 2 := by norm_num [UScalar.ofNatCore_val_eq]
  obtain ⟨z, hz, _⟩ := mul_ok (2#u64) u (by rw [h2, max64]; omega)
  exact ⟨z, hz, trivial⟩

/-- Site 5: 3 * P. -/
theorem three_P_ok :
    ∃ z, (3#u64 * core.convert.num.FromU64U32.from AspisR72Sampler.field.P : Result U64) = ok z ∧ True := by
  have h3 : (3#u64 : U64).val = 3 := by norm_num [UScalar.ofNatCore_val_eq]
  obtain ⟨z, hz, _⟩ := mul_ok (3#u64) (core.convert.num.FromU64U32.from AspisR72Sampler.field.P)
    (by rw [h3, from_val, P_val, max64]; omega)
  exact ⟨z, hz, trivial⟩

/-- Site class 6: the M31 reduction of any U64 (four sites). -/
theorem reduce_ok (x : U64) : ∃ y, AspisR72Sampler.field.M31.reduce_u64 x = ok y ∧ True := by
  obtain ⟨y, hy, _⟩ := refReduce_total x
  exact ⟨y, by rw [R72_reduce_wrapper]; exact hy, trivial⟩

theorem new_ok (a b : AspisR72Sampler.field.M31) :
    ∃ z, AspisR72Sampler.field.CM31.new a b = ok z ∧ True := ⟨{ a, b }, rfl, trivial⟩

/-- TOTAL (a): r24_canonical_mul is ok for EVERY pair of inputs. -/
theorem r24_canonical_mul_total (left right : AspisR72Sampler.field.QM31) :
    ∃ out : Option AspisR72Sampler.field.QM31,
      AspisR72Sampler.field.r24_canonical_mul left right = .ok out := by
  unfold AspisR72Sampler.field.r24_canonical_mul
  dsimp only
  simp only [lift, bind_tc_ok]
  by_cases hg0 : left.c0.a ≥ AspisR72Sampler.field.P
  · rw [if_pos hg0]; exact ⟨none, rfl⟩
  rw [if_neg hg0]
  by_cases hg1 : left.c0.b ≥ AspisR72Sampler.field.P
  · rw [if_pos hg1]; exact ⟨none, rfl⟩
  rw [if_neg hg1]
  by_cases hg2 : left.c1.a ≥ AspisR72Sampler.field.P
  · rw [if_pos hg2]; exact ⟨none, rfl⟩
  rw [if_neg hg2]
  by_cases hg3 : left.c1.b ≥ AspisR72Sampler.field.P
  · rw [if_pos hg3]; exact ⟨none, rfl⟩
  rw [if_neg hg3]
  by_cases hg4 : right.c0.a ≥ AspisR72Sampler.field.P
  · rw [if_pos hg4]; exact ⟨none, rfl⟩
  rw [if_neg hg4]
  by_cases hg5 : right.c0.b ≥ AspisR72Sampler.field.P
  · rw [if_pos hg5]; exact ⟨none, rfl⟩
  rw [if_neg hg5]
  by_cases hg6 : right.c1.a ≥ AspisR72Sampler.field.P
  · rw [if_pos hg6]; exact ⟨none, rfl⟩
  rw [if_neg hg6]
  by_cases hg7 : right.c1.b ≥ AspisR72Sampler.field.P
  · rw [if_pos hg7]; exact ⟨none, rfl⟩
  rw [if_neg hg7]
  refine step (limb_mul_ok _ _) (fun i _ => ?_)
  refine step PP_ok (fun pp hpp => ?_)
  refine step (limb_mul_ok _ _) (fun i3 _ => ?_)
  refine step (closure_ok _ _) (fun u hu => ?_)
  refine step (limb_mul_ok _ _) (fun i5 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i6 _ => ?_)
  refine step (closure_ok _ _) (fun v hv => ?_)
  refine step (limb_mul_ok _ _) (fun i8 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i10 _ => ?_)
  refine step (two_mul_ok u (by omega)) (fun i12 _ => ?_)
  refine step three_P_ok (fun i15 _ => ?_)
  refine step (reduce_ok _) (fun out0 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i18 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i19 _ => ?_)
  refine step (two_mul_ok v (by omega)) (fun i22 _ => ?_)
  refine step (reduce_ok _) (fun out1 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i24 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i25 _ => ?_)
  refine step (two_mul_ok pp (by omega)) (fun i27 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i29 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i31 _ => ?_)
  refine step (reduce_ok _) (fun out2 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i33 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i34 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i36 _ => ?_)
  refine step (limb_mul_ok _ _) (fun i38 _ => ?_)
  refine step (reduce_ok _) (fun out3 _ => ?_)
  refine step (new_ok _ _) (fun c2 _ => ?_)
  refine step (new_ok _ _) (fun c3 _ => ?_)
  exact ⟨_, rfl⟩

end AspisR1.NPS_R24Total
