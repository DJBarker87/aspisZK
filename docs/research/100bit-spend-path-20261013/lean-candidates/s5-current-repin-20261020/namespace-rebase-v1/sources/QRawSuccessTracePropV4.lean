import Aeneas
import AspisR1CanonicalQRawUnified.Funs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace AspisR1CanonicalQRawUnified.Proof

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

def QRawSuccessTrace (self rhs : canonical.Q) (out : Array Std.U64 4#usize) : Prop :=
  ∃ (v_a : Array Std.U64 4#usize),
  ∃ (v_a1 : Std.U64),
  ∃ (v_b : Std.U64),
  ∃ (v_c : Std.U64),
  ∃ (v_d : Std.U64),
  ∃ (v_a2 : Array Std.U64 4#usize),
  ∃ (v_e : Std.U64),
  ∃ (v_f : Std.U64),
  ∃ (v_g : Std.U64),
  ∃ (v_h : Std.U64),
  ∃ (v_i : Std.U64),
  ∃ (v_i1 : Std.U64),
  ∃ (v_i2 : Std.U64),
  ∃ (v_i3 : Std.U64),
  ∃ (v_i4 : Std.U64),
  ∃ (v_u : Std.U64),
  ∃ (v_i5 : Std.U64),
  ∃ (v_i6 : Std.U64),
  ∃ (v_i7 : Std.U64),
  ∃ (v_v : Std.U64),
  ∃ (v_i8 : Std.U64),
  ∃ (v_i9 : Std.U64),
  ∃ (v_i10 : Std.U64),
  ∃ (v_i11 : Std.U64),
  ∃ (v_i12 : Std.U64),
  ∃ (v_i13 : Std.U64),
  ∃ (v_i14 : Std.U64),
  ∃ (v_i15 : Std.U64),
  ∃ (v_i16 : Std.U64),
  ∃ (v_i17 : Std.U64),
  ∃ (v_i18 : Std.U64),
  ∃ (v_i19 : Std.U64),
  ∃ (v_i20 : Std.U64),
  ∃ (v_i21 : Std.U64),
  ∃ (v_i22 : Std.U64),
  ∃ (v_i23 : Std.U64),
  ∃ (v_i24 : Std.U64),
  ∃ (v_i25 : Std.U64),
  ∃ (v_i26 : Std.U64),
  ∃ (v_i27 : Std.U64),
  ∃ (v_i28 : Std.U64),
  ∃ (v_i29 : Std.U64),
  ∃ (v_i30 : Std.U64),
  ∃ (v_i31 : Std.U64),
  ∃ (v_i32 : Std.U64),
  ∃ (v_i33 : Std.U64),
  ∃ (v_i34 : Std.U64),
  ∃ (v_i35 : Std.U64),
  ∃ (v_i36 : Std.U64),
  ∃ (v_i37 : Std.U64),
  ∃ (v_i38 : Std.U64),
  ∃ (v_i39 : Std.U64),
  (
     core.array.Array.map canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 self () = Result.ok v_a ∧
    Array.index_usize v_a 0#usize = Result.ok v_a1 ∧
    Array.index_usize v_a 1#usize = Result.ok v_b ∧
    Array.index_usize v_a 2#usize = Result.ok v_c ∧
    Array.index_usize v_a 3#usize = Result.ok v_d ∧
     core.array.Array.map canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 rhs () = Result.ok v_a2 ∧
    Array.index_usize v_a2 0#usize = Result.ok v_e ∧
    Array.index_usize v_a2 1#usize = Result.ok v_f ∧
    Array.index_usize v_a2 2#usize = Result.ok v_g ∧
    Array.index_usize v_a2 3#usize = Result.ok v_h ∧
    v_c * v_g = Result.ok v_i ∧
    canonical.Q.raw.PP = Result.ok v_i1 ∧
    lift (core.num.U64.wrapping_add v_i v_i1) = Result.ok v_i2 ∧
    v_d * v_h = Result.ok v_i3 ∧
    lift (core.num.U64.wrapping_sub v_i2 v_i3) = Result.ok v_i4 ∧
     canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () v_i4 = Result.ok v_u ∧
    v_c * v_h = Result.ok v_i5 ∧
    v_d * v_g = Result.ok v_i6 ∧
    lift (core.num.U64.wrapping_add v_i5 v_i6) = Result.ok v_i7 ∧
     canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () v_i7 = Result.ok v_v ∧
    v_a1 * v_e = Result.ok v_i8 ∧
    lift (core.num.U64.wrapping_add v_i8 v_i1) = Result.ok v_i9 ∧
    v_b * v_f = Result.ok v_i10 ∧
    lift (core.num.U64.wrapping_sub v_i9 v_i10) = Result.ok v_i11 ∧
    2#u64 * v_u = Result.ok v_i12 ∧
    lift (core.num.U64.wrapping_add v_i11 v_i12) = Result.ok v_i13 ∧
    lift (core.convert.num.FromU64U32.from canonical.P) = Result.ok v_i14 ∧
    3#u64 * v_i14 = Result.ok v_i15 ∧
    lift (core.num.U64.wrapping_add v_i13 v_i15) = Result.ok v_i16 ∧
    lift (core.num.U64.wrapping_sub v_i16 v_v) = Result.ok v_i17 ∧
    v_a1 * v_f = Result.ok v_i18 ∧
    v_b * v_e = Result.ok v_i19 ∧
    lift (core.num.U64.wrapping_add v_i18 v_i19) = Result.ok v_i20 ∧
    lift (core.num.U64.wrapping_add v_i20 v_u) = Result.ok v_i21 ∧
    2#u64 * v_v = Result.ok v_i22 ∧
    lift (core.num.U64.wrapping_add v_i21 v_i22) = Result.ok v_i23 ∧
    v_a1 * v_g = Result.ok v_i24 ∧
    v_c * v_e = Result.ok v_i25 ∧
    lift (core.num.U64.wrapping_add v_i24 v_i25) = Result.ok v_i26 ∧
    2#u64 * v_i1 = Result.ok v_i27 ∧
    lift (core.num.U64.wrapping_add v_i26 v_i27) = Result.ok v_i28 ∧
    v_b * v_h = Result.ok v_i29 ∧
    lift (core.num.U64.wrapping_sub v_i28 v_i29) = Result.ok v_i30 ∧
    v_d * v_f = Result.ok v_i31 ∧
    lift (core.num.U64.wrapping_sub v_i30 v_i31) = Result.ok v_i32 ∧
    v_a1 * v_h = Result.ok v_i33 ∧
    v_b * v_g = Result.ok v_i34 ∧
    lift (core.num.U64.wrapping_add v_i33 v_i34) = Result.ok v_i35 ∧
    v_c * v_f = Result.ok v_i36 ∧
    lift (core.num.U64.wrapping_add v_i35 v_i36) = Result.ok v_i37 ∧
    v_d * v_e = Result.ok v_i38 ∧
    lift (core.num.U64.wrapping_add v_i37 v_i38) = Result.ok v_i39 ∧
    out = Array.make 4#usize [v_i17, v_i23, v_i32, v_i39]
  )

theorem qraw_success_trace (self rhs : canonical.Q) (out : Array Std.U64 4#usize)
    (hraw : canonical.Q.raw self rhs = .ok out) : QRawSuccessTrace self rhs out := by
  unfold canonical.Q.raw at hraw
  rcases bind_ok_inv hraw with ⟨v_a, h_a, hrest1⟩
  rcases bind_ok_inv hrest1 with ⟨v_a1, h_a1, hrest2⟩
  rcases bind_ok_inv hrest2 with ⟨v_b, h_b, hrest3⟩
  rcases bind_ok_inv hrest3 with ⟨v_c, h_c, hrest4⟩
  rcases bind_ok_inv hrest4 with ⟨v_d, h_d, hrest5⟩
  rcases bind_ok_inv hrest5 with ⟨v_a2, h_a2, hrest6⟩
  rcases bind_ok_inv hrest6 with ⟨v_e, h_e, hrest7⟩
  rcases bind_ok_inv hrest7 with ⟨v_f, h_f, hrest8⟩
  rcases bind_ok_inv hrest8 with ⟨v_g, h_g, hrest9⟩
  rcases bind_ok_inv hrest9 with ⟨v_h, h_h, hrest10⟩
  rcases bind_ok_inv hrest10 with ⟨v_i, h_i, hrest11⟩
  rcases bind_ok_inv hrest11 with ⟨v_i1, h_i1, hrest12⟩
  rcases bind_ok_inv hrest12 with ⟨v_i2, h_i2, hrest13⟩
  rcases bind_ok_inv hrest13 with ⟨v_i3, h_i3, hrest14⟩
  rcases bind_ok_inv hrest14 with ⟨v_i4, h_i4, hrest15⟩
  rcases bind_ok_inv hrest15 with ⟨v_u, h_u, hrest16⟩
  rcases bind_ok_inv hrest16 with ⟨v_i5, h_i5, hrest17⟩
  rcases bind_ok_inv hrest17 with ⟨v_i6, h_i6, hrest18⟩
  rcases bind_ok_inv hrest18 with ⟨v_i7, h_i7, hrest19⟩
  rcases bind_ok_inv hrest19 with ⟨v_v, h_v, hrest20⟩
  rcases bind_ok_inv hrest20 with ⟨v_i8, h_i8, hrest21⟩
  rcases bind_ok_inv hrest21 with ⟨v_i9, h_i9, hrest22⟩
  rcases bind_ok_inv hrest22 with ⟨v_i10, h_i10, hrest23⟩
  rcases bind_ok_inv hrest23 with ⟨v_i11, h_i11, hrest24⟩
  rcases bind_ok_inv hrest24 with ⟨v_i12, h_i12, hrest25⟩
  rcases bind_ok_inv hrest25 with ⟨v_i13, h_i13, hrest26⟩
  rcases bind_ok_inv hrest26 with ⟨v_i14, h_i14, hrest27⟩
  rcases bind_ok_inv hrest27 with ⟨v_i15, h_i15, hrest28⟩
  rcases bind_ok_inv hrest28 with ⟨v_i16, h_i16, hrest29⟩
  rcases bind_ok_inv hrest29 with ⟨v_i17, h_i17, hrest30⟩
  rcases bind_ok_inv hrest30 with ⟨v_i18, h_i18, hrest31⟩
  rcases bind_ok_inv hrest31 with ⟨v_i19, h_i19, hrest32⟩
  rcases bind_ok_inv hrest32 with ⟨v_i20, h_i20, hrest33⟩
  rcases bind_ok_inv hrest33 with ⟨v_i21, h_i21, hrest34⟩
  rcases bind_ok_inv hrest34 with ⟨v_i22, h_i22, hrest35⟩
  rcases bind_ok_inv hrest35 with ⟨v_i23, h_i23, hrest36⟩
  rcases bind_ok_inv hrest36 with ⟨v_i24, h_i24, hrest37⟩
  rcases bind_ok_inv hrest37 with ⟨v_i25, h_i25, hrest38⟩
  rcases bind_ok_inv hrest38 with ⟨v_i26, h_i26, hrest39⟩
  rcases bind_ok_inv hrest39 with ⟨v_i27, h_i27, hrest40⟩
  rcases bind_ok_inv hrest40 with ⟨v_i28, h_i28, hrest41⟩
  rcases bind_ok_inv hrest41 with ⟨v_i29, h_i29, hrest42⟩
  rcases bind_ok_inv hrest42 with ⟨v_i30, h_i30, hrest43⟩
  rcases bind_ok_inv hrest43 with ⟨v_i31, h_i31, hrest44⟩
  rcases bind_ok_inv hrest44 with ⟨v_i32, h_i32, hrest45⟩
  rcases bind_ok_inv hrest45 with ⟨v_i33, h_i33, hrest46⟩
  rcases bind_ok_inv hrest46 with ⟨v_i34, h_i34, hrest47⟩
  rcases bind_ok_inv hrest47 with ⟨v_i35, h_i35, hrest48⟩
  rcases bind_ok_inv hrest48 with ⟨v_i36, h_i36, hrest49⟩
  rcases bind_ok_inv hrest49 with ⟨v_i37, h_i37, hrest50⟩
  rcases bind_ok_inv hrest50 with ⟨v_i38, h_i38, hrest51⟩
  rcases bind_ok_inv hrest51 with ⟨v_i39, h_i39, hrest52⟩
  have hout : Result.ok (Array.make 4#usize [v_i17, v_i23, v_i32, v_i39]) = Result.ok out := hrest52
  have houtEq := Result.ok.inj hout
  dsimp [QRawSuccessTrace]
  refine ⟨v_a, ?_⟩
  refine ⟨v_a1, ?_⟩
  refine ⟨v_b, ?_⟩
  refine ⟨v_c, ?_⟩
  refine ⟨v_d, ?_⟩
  refine ⟨v_a2, ?_⟩
  refine ⟨v_e, ?_⟩
  refine ⟨v_f, ?_⟩
  refine ⟨v_g, ?_⟩
  refine ⟨v_h, ?_⟩
  refine ⟨v_i, ?_⟩
  refine ⟨v_i1, ?_⟩
  refine ⟨v_i2, ?_⟩
  refine ⟨v_i3, ?_⟩
  refine ⟨v_i4, ?_⟩
  refine ⟨v_u, ?_⟩
  refine ⟨v_i5, ?_⟩
  refine ⟨v_i6, ?_⟩
  refine ⟨v_i7, ?_⟩
  refine ⟨v_v, ?_⟩
  refine ⟨v_i8, ?_⟩
  refine ⟨v_i9, ?_⟩
  refine ⟨v_i10, ?_⟩
  refine ⟨v_i11, ?_⟩
  refine ⟨v_i12, ?_⟩
  refine ⟨v_i13, ?_⟩
  refine ⟨v_i14, ?_⟩
  refine ⟨v_i15, ?_⟩
  refine ⟨v_i16, ?_⟩
  refine ⟨v_i17, ?_⟩
  refine ⟨v_i18, ?_⟩
  refine ⟨v_i19, ?_⟩
  refine ⟨v_i20, ?_⟩
  refine ⟨v_i21, ?_⟩
  refine ⟨v_i22, ?_⟩
  refine ⟨v_i23, ?_⟩
  refine ⟨v_i24, ?_⟩
  refine ⟨v_i25, ?_⟩
  refine ⟨v_i26, ?_⟩
  refine ⟨v_i27, ?_⟩
  refine ⟨v_i28, ?_⟩
  refine ⟨v_i29, ?_⟩
  refine ⟨v_i30, ?_⟩
  refine ⟨v_i31, ?_⟩
  refine ⟨v_i32, ?_⟩
  refine ⟨v_i33, ?_⟩
  refine ⟨v_i34, ?_⟩
  refine ⟨v_i35, ?_⟩
  refine ⟨v_i36, ?_⟩
  refine ⟨v_i37, ?_⟩
  refine ⟨v_i38, ?_⟩
  refine ⟨v_i39, ?_⟩
  exact ⟨
    h_a,
    h_a1,
    h_b,
    h_c,
    h_d,
    h_a2,
    h_e,
    h_f,
    h_g,
    h_h,
    h_i,
    h_i1,
    h_i2,
    h_i3,
    h_i4,
    h_u,
    h_i5,
    h_i6,
    h_i7,
    h_v,
    h_i8,
    h_i9,
    h_i10,
    h_i11,
    h_i12,
    h_i13,
    h_i14,
    h_i15,
    h_i16,
    h_i17,
    h_i18,
    h_i19,
    h_i20,
    h_i21,
    h_i22,
    h_i23,
    h_i24,
    h_i25,
    h_i26,
    h_i27,
    h_i28,
    h_i29,
    h_i30,
    h_i31,
    h_i32,
    h_i33,
    h_i34,
    h_i35,
    h_i36,
    h_i37,
    h_i38,
    h_i39,
    houtEq.symm
  ⟩

#print axioms qraw_success_trace
end AspisR1CanonicalQRawUnified.Proof
