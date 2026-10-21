import S5QRaw.SuccessTracePropV4
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CanonicalQRawUnified.Proof

def QRawTraceBody (self rhs : canonical.Q) (out : Array Std.U64 4#usize)
    (v_a : Array Std.U64 4#usize)
    (v_a1 : Std.U64)
    (v_b : Std.U64)
    (v_c : Std.U64)
    (v_d : Std.U64)
    (v_a2 : Array Std.U64 4#usize)
    (v_e : Std.U64)
    (v_f : Std.U64)
    (v_g : Std.U64)
    (v_h : Std.U64)
    (v_i : Std.U64)
    (v_i1 : Std.U64)
    (v_i2 : Std.U64)
    (v_i3 : Std.U64)
    (v_i4 : Std.U64)
    (v_u : Std.U64)
    (v_i5 : Std.U64)
    (v_i6 : Std.U64)
    (v_i7 : Std.U64)
    (v_v : Std.U64)
    (v_i8 : Std.U64)
    (v_i9 : Std.U64)
    (v_i10 : Std.U64)
    (v_i11 : Std.U64)
    (v_i12 : Std.U64)
    (v_i13 : Std.U64)
    (v_i14 : Std.U64)
    (v_i15 : Std.U64)
    (v_i16 : Std.U64)
    (v_i17 : Std.U64)
    (v_i18 : Std.U64)
    (v_i19 : Std.U64)
    (v_i20 : Std.U64)
    (v_i21 : Std.U64)
    (v_i22 : Std.U64)
    (v_i23 : Std.U64)
    (v_i24 : Std.U64)
    (v_i25 : Std.U64)
    (v_i26 : Std.U64)
    (v_i27 : Std.U64)
    (v_i28 : Std.U64)
    (v_i29 : Std.U64)
    (v_i30 : Std.U64)
    (v_i31 : Std.U64)
    (v_i32 : Std.U64)
    (v_i33 : Std.U64)
    (v_i34 : Std.U64)
    (v_i35 : Std.U64)
    (v_i36 : Std.U64)
    (v_i37 : Std.U64)
    (v_i38 : Std.U64)
    (v_i39 : Std.U64) : Prop :=
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

def QRawNoWrapFacts (self rhs : canonical.Q) (out : Array Std.U64 4#usize) : Prop :=
  ∀ (v_a : Array Std.U64 4#usize)
    (v_a1 : Std.U64) (v_b : Std.U64) (v_c : Std.U64) (v_d : Std.U64)
    (v_a2 : Array Std.U64 4#usize)
    (v_e : Std.U64) (v_f : Std.U64) (v_g : Std.U64) (v_h : Std.U64)
    (v_i : Std.U64) (v_i1 : Std.U64) (v_i2 : Std.U64) (v_i3 : Std.U64) (v_i4 : Std.U64)
    (v_u : Std.U64) (v_i5 : Std.U64) (v_i6 : Std.U64) (v_i7 : Std.U64)
    (v_v : Std.U64) (v_i8 : Std.U64) (v_i9 : Std.U64) (v_i10 : Std.U64)
    (v_i11 : Std.U64) (v_i12 : Std.U64) (v_i13 : Std.U64) (v_i14 : Std.U64)
    (v_i15 : Std.U64) (v_i16 : Std.U64) (v_i17 : Std.U64) (v_i18 : Std.U64)
    (v_i19 : Std.U64) (v_i20 : Std.U64) (v_i21 : Std.U64) (v_i22 : Std.U64)
    (v_i23 : Std.U64) (v_i24 : Std.U64) (v_i25 : Std.U64) (v_i26 : Std.U64)
    (v_i27 : Std.U64) (v_i28 : Std.U64) (v_i29 : Std.U64) (v_i30 : Std.U64)
    (v_i31 : Std.U64) (v_i32 : Std.U64) (v_i33 : Std.U64) (v_i34 : Std.U64)
    (v_i35 : Std.U64) (v_i36 : Std.U64) (v_i37 : Std.U64) (v_i38 : Std.U64)
    (v_i39 : Std.U64),
    QRawTraceBody self rhs out v_a v_a1 v_b v_c v_d v_a2 v_e v_f v_g v_h v_i v_i1 v_i2 v_i3 v_i4 v_u v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11 v_i12 v_i13 v_i14 v_i15 v_i16 v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23 v_i24 v_i25 v_i26 v_i27 v_i28 v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35 v_i36 v_i37 v_i38 v_i39 →
    (v_i.val + v_i1.val < 2^64 ∧
    v_i3.val ≤ v_i2.val ∧
    v_i5.val + v_i6.val < 2^64 ∧
    v_i8.val + v_i1.val < 2^64 ∧
    v_i10.val ≤ v_i9.val ∧
    v_i11.val + v_i12.val < 2^64 ∧
    v_i13.val + v_i15.val < 2^64 ∧
    v_v.val ≤ v_i16.val ∧
    v_i18.val + v_i19.val < 2^64 ∧
    v_i20.val + v_u.val < 2^64 ∧
    v_i21.val + v_i22.val < 2^64 ∧
    v_i24.val + v_i25.val < 2^64 ∧
    v_i26.val + v_i27.val < 2^64 ∧
    v_i29.val ≤ v_i28.val ∧
    v_i31.val ≤ v_i30.val ∧
    v_i33.val + v_i34.val < 2^64 ∧
    v_i35.val + v_i36.val < 2^64 ∧
    v_i37.val + v_i38.val < 2^64)
theorem qraw_success_trace_wrap_guards (self rhs : canonical.Q)
    (out : Array Std.U64 4#usize) (hraw : canonical.Q.raw self rhs = .ok out)
    (hguards : QRawNoWrapFacts self rhs out) :
    ∃ (v_a : Array Std.U64 4#usize)
    (v_a1 : Std.U64)
    (v_b : Std.U64)
    (v_c : Std.U64)
    (v_d : Std.U64)
    (v_a2 : Array Std.U64 4#usize)
    (v_e : Std.U64)
    (v_f : Std.U64)
    (v_g : Std.U64)
    (v_h : Std.U64)
    (v_i : Std.U64)
    (v_i1 : Std.U64)
    (v_i2 : Std.U64)
    (v_i3 : Std.U64)
    (v_i4 : Std.U64)
    (v_u : Std.U64)
    (v_i5 : Std.U64)
    (v_i6 : Std.U64)
    (v_i7 : Std.U64)
    (v_v : Std.U64)
    (v_i8 : Std.U64)
    (v_i9 : Std.U64)
    (v_i10 : Std.U64)
    (v_i11 : Std.U64)
    (v_i12 : Std.U64)
    (v_i13 : Std.U64)
    (v_i14 : Std.U64)
    (v_i15 : Std.U64)
    (v_i16 : Std.U64)
    (v_i17 : Std.U64)
    (v_i18 : Std.U64)
    (v_i19 : Std.U64)
    (v_i20 : Std.U64)
    (v_i21 : Std.U64)
    (v_i22 : Std.U64)
    (v_i23 : Std.U64)
    (v_i24 : Std.U64)
    (v_i25 : Std.U64)
    (v_i26 : Std.U64)
    (v_i27 : Std.U64)
    (v_i28 : Std.U64)
    (v_i29 : Std.U64)
    (v_i30 : Std.U64)
    (v_i31 : Std.U64)
    (v_i32 : Std.U64)
    (v_i33 : Std.U64)
    (v_i34 : Std.U64)
    (v_i35 : Std.U64)
    (v_i36 : Std.U64)
    (v_i37 : Std.U64)
    (v_i38 : Std.U64)
    (v_i39 : Std.U64),
      QRawTraceBody self rhs out v_a v_a1 v_b v_c v_d v_a2 v_e v_f v_g v_h v_i v_i1 v_i2 v_i3 v_i4 v_u v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11 v_i12 v_i13 v_i14 v_i15 v_i16 v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23 v_i24 v_i25 v_i26 v_i27 v_i28 v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35 v_i36 v_i37 v_i38 v_i39 ∧
      (v_i.val + v_i1.val < 2^64 ∧
    v_i3.val ≤ v_i2.val ∧
    v_i5.val + v_i6.val < 2^64 ∧
    v_i8.val + v_i1.val < 2^64 ∧
    v_i10.val ≤ v_i9.val ∧
    v_i11.val + v_i12.val < 2^64 ∧
    v_i13.val + v_i15.val < 2^64 ∧
    v_v.val ≤ v_i16.val ∧
    v_i18.val + v_i19.val < 2^64 ∧
    v_i20.val + v_u.val < 2^64 ∧
    v_i21.val + v_i22.val < 2^64 ∧
    v_i24.val + v_i25.val < 2^64 ∧
    v_i26.val + v_i27.val < 2^64 ∧
    v_i29.val ≤ v_i28.val ∧
    v_i31.val ≤ v_i30.val ∧
    v_i33.val + v_i34.val < 2^64 ∧
    v_i35.val + v_i36.val < 2^64 ∧
    v_i37.val + v_i38.val < 2^64) := by
  rcases qraw_success_trace self rhs out hraw with
    ⟨v_a, v_a1, v_b, v_c, v_d, v_a2, v_e, v_f, v_g, v_h, v_i, v_i1, v_i2, v_i3, v_i4, v_u, v_i5, v_i6, v_i7, v_v, v_i8, v_i9, v_i10, v_i11, v_i12, v_i13, v_i14, v_i15, v_i16, v_i17, v_i18, v_i19, v_i20, v_i21, v_i22, v_i23, v_i24, v_i25, v_i26, v_i27, v_i28, v_i29, v_i30, v_i31, v_i32, v_i33, v_i34, v_i35, v_i36, v_i37, v_i38, v_i39, hbody⟩
  exact ⟨v_a, v_a1, v_b, v_c, v_d, v_a2, v_e, v_f, v_g, v_h, v_i, v_i1, v_i2, v_i3, v_i4, v_u, v_i5, v_i6, v_i7, v_v, v_i8, v_i9, v_i10, v_i11, v_i12, v_i13, v_i14, v_i15, v_i16, v_i17, v_i18, v_i19, v_i20, v_i21, v_i22, v_i23, v_i24, v_i25, v_i26, v_i27, v_i28, v_i29, v_i30, v_i31, v_i32, v_i33, v_i34, v_i35, v_i36, v_i37, v_i38, v_i39, hbody, hguards v_a v_a1 v_b v_c v_d v_a2 v_e v_f v_g v_h v_i v_i1 v_i2 v_i3 v_i4 v_u v_i5 v_i6 v_i7 v_v v_i8 v_i9 v_i10 v_i11 v_i12 v_i13 v_i14 v_i15 v_i16 v_i17 v_i18 v_i19 v_i20 v_i21 v_i22 v_i23 v_i24 v_i25 v_i26 v_i27 v_i28 v_i29 v_i30 v_i31 v_i32 v_i33 v_i34 v_i35 v_i36 v_i37 v_i38 v_i39 hbody⟩

#print axioms qraw_success_trace_wrap_guards
end AspisR1CanonicalQRawUnified.Proof
