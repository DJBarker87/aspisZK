import AspisR1S9ActualRawCutV1.Funs
import QRawSourceForwardTotalityV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualRawKernelsV1
abbrev A4 := Array U32 4#usize
abbrev R4 := Array U64 4#usize
abbrev cv := core.convert.num.FromU64U32.from
abbrev Kernel := U64 → U64 → U64 → U64 → U64 → U64 → U64 → U64 → Result R4
/-- Exact retained source tail; irreducibility seals symbolic arithmetic during input specialization. -/
@[irreducible] def checkedKernel (a1 b c d e f g h : U64) : Result R4 := do
  let i ← c * g
  let i1 ← AspisR1CanonicalQRawUnified.canonical.Q.raw.PP
  let i2 ← lift (core.num.U64.wrapping_add i i1)
  let i3 ← d * h
  let i4 ← lift (core.num.U64.wrapping_sub i2 i3)
  let u ←
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () i4
  let i5 ← c * h
  let i6 ← d * g
  let i7 ← lift (core.num.U64.wrapping_add i5 i6)
  let v ←
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () i7
  let i8 ← a1 * e
  let i9 ← lift (core.num.U64.wrapping_add i8 i1)
  let i10 ← b * f
  let i11 ← lift (core.num.U64.wrapping_sub i9 i10)
  let i12 ← 2#u64 * u
  let i13 ← lift (core.num.U64.wrapping_add i11 i12)
  let i14 ← lift (core.convert.num.FromU64U32.from AspisR1CanonicalQRawUnified.canonical.P)
  let i15 ← 3#u64 * i14
  let i16 ← lift (core.num.U64.wrapping_add i13 i15)
  let i17 ← lift (core.num.U64.wrapping_sub i16 v)
  let i18 ← a1 * f
  let i19 ← b * e
  let i20 ← lift (core.num.U64.wrapping_add i18 i19)
  let i21 ← lift (core.num.U64.wrapping_add i20 u)
  let i22 ← 2#u64 * v
  let i23 ← lift (core.num.U64.wrapping_add i21 i22)
  let i24 ← a1 * g
  let i25 ← c * e
  let i26 ← lift (core.num.U64.wrapping_add i24 i25)
  let i27 ← 2#u64 * i1
  let i28 ← lift (core.num.U64.wrapping_add i26 i27)
  let i29 ← b * h
  let i30 ← lift (core.num.U64.wrapping_sub i28 i29)
  let i31 ← d * f
  let i32 ← lift (core.num.U64.wrapping_sub i30 i31)
  let i33 ← a1 * h
  let i34 ← b * g
  let i35 ← lift (core.num.U64.wrapping_add i33 i34)
  let i36 ← c * f
  let i37 ← lift (core.num.U64.wrapping_add i35 i36)
  let i38 ← d * e
  let i39 ← lift (core.num.U64.wrapping_add i37 i38)
  ok (Array.make 4#usize [ i17, i23, i32, i39 ])

/-- Exact actual release source tail; no arithmetic operator edits. -/
@[irreducible] def actualKernel (a b c d e f g h : U64) : Result R4 := do
  let i16 ← lift (Std.U64.wrapping_mul c g)
  let i17 ← AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw.PP
  let i18 ← lift (core.num.U64.wrapping_add i16 i17)
  let i19 ← lift (Std.U64.wrapping_mul d h)
  let i20 ← lift (core.num.U64.wrapping_sub i18 i19)
  let u ←
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
      () i20
  let i21 ← lift (Std.U64.wrapping_mul c h)
  let i22 ← lift (Std.U64.wrapping_mul d g)
  let i23 ← lift (core.num.U64.wrapping_add i21 i22)
  let v ←
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
      () i23
  let i24 ← lift (Std.U64.wrapping_mul a e)
  let i25 ← lift (core.num.U64.wrapping_add i24 i17)
  let i26 ← lift (Std.U64.wrapping_mul b f)
  let i27 ← lift (core.num.U64.wrapping_sub i25 i26)
  let i28 ← lift (Std.U64.wrapping_mul 2#u64 u)
  let i29 ← lift (core.num.U64.wrapping_add i27 i28)
  let i30 ← lift (core.convert.num.FromU64U32.from AspisR1S9ActualRawCutV1.fast_pairing.canonical.P)
  let i31 ← lift (Std.U64.wrapping_mul 3#u64 i30)
  let i32 ← lift (core.num.U64.wrapping_add i29 i31)
  let i33 ← lift (core.num.U64.wrapping_sub i32 v)
  let i34 ← lift (Std.U64.wrapping_mul a f)
  let i35 ← lift (Std.U64.wrapping_mul b e)
  let i36 ← lift (core.num.U64.wrapping_add i34 i35)
  let i37 ← lift (core.num.U64.wrapping_add i36 u)
  let i38 ← lift (Std.U64.wrapping_mul 2#u64 v)
  let i39 ← lift (core.num.U64.wrapping_add i37 i38)
  let i40 ← lift (Std.U64.wrapping_mul a g)
  let i41 ← lift (Std.U64.wrapping_mul c e)
  let i42 ← lift (core.num.U64.wrapping_add i40 i41)
  let i43 ← lift (Std.U64.wrapping_mul 2#u64 i17)
  let i44 ← lift (core.num.U64.wrapping_add i42 i43)
  let i45 ← lift (Std.U64.wrapping_mul b h)
  let i46 ← lift (core.num.U64.wrapping_sub i44 i45)
  let i47 ← lift (Std.U64.wrapping_mul d f)
  let i48 ← lift (core.num.U64.wrapping_sub i46 i47)
  let i49 ← lift (Std.U64.wrapping_mul a h)
  let i50 ← lift (Std.U64.wrapping_mul b g)
  let i51 ← lift (core.num.U64.wrapping_add i49 i50)
  let i52 ← lift (Std.U64.wrapping_mul c f)
  let i53 ← lift (core.num.U64.wrapping_add i51 i52)
  let i54 ← lift (Std.U64.wrapping_mul d e)
  let i55 ← lift (core.num.U64.wrapping_add i53 i54)
  ok (Array.make 4#usize [ i33, i39, i48, i55 ])

/-- Exact retained model input prefix with its arithmetic continuation explicit. -/
def checkedPrefix (kernel : Kernel) (self rhs : A4) : Result R4 := do
  let a ←
    core.array.Array.map
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 self ()
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let a2 ←
    core.array.Array.map
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 rhs ()
  let e ← Array.index_usize a2 0#usize
  let f ← Array.index_usize a2 1#usize
  let g ← Array.index_usize a2 2#usize
  let h ← Array.index_usize a2 3#usize
  kernel a1 b c d e f g h
/-- Exact actual direct-read prefix with its arithmetic continuation explicit. -/
def actualPrefix (kernel : Kernel) (self rhs : A4) : Result R4 := do
  let i ← Array.index_usize self 0#usize
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 ← Array.index_usize self 1#usize
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← Array.index_usize self 2#usize
  let i5 ← lift (core.convert.num.FromU64U32.from i4)
  let i6 ← Array.index_usize self 3#usize
  let i7 ← lift (core.convert.num.FromU64U32.from i6)
  let a ← Array.index_usize (Array.make 4#usize [ i1, i3, i5, i7 ]) 0#usize
  let b ← Array.index_usize (Array.make 4#usize [ i1, i3, i5, i7 ]) 1#usize
  let c ← Array.index_usize (Array.make 4#usize [ i1, i3, i5, i7 ]) 2#usize
  let d ← Array.index_usize (Array.make 4#usize [ i1, i3, i5, i7 ]) 3#usize
  let i8 ← Array.index_usize rhs 0#usize
  let i9 ← lift (core.convert.num.FromU64U32.from i8)
  let i10 ← Array.index_usize rhs 1#usize
  let i11 ← lift (core.convert.num.FromU64U32.from i10)
  let i12 ← Array.index_usize rhs 2#usize
  let i13 ← lift (core.convert.num.FromU64U32.from i12)
  let i14 ← Array.index_usize rhs 3#usize
  let i15 ← lift (core.convert.num.FromU64U32.from i14)
  let e ←
    Array.index_usize (Array.make 4#usize [ i9, i11, i13, i15 ]) 0#usize
  let f ←
    Array.index_usize (Array.make 4#usize [ i9, i11, i13, i15 ]) 1#usize
  let g ←
    Array.index_usize (Array.make 4#usize [ i9, i11, i13, i15 ]) 2#usize
  let h ←
    Array.index_usize (Array.make 4#usize [ i9, i11, i13, i15 ]) 3#usize
  kernel a b c d e f g h

theorem checked_raw_factor (self rhs : A4) :
    AspisR1CanonicalQRawUnified.canonical.Q.raw self rhs =
      checkedPrefix checkedKernel self rhs := by
  unfold AspisR1CanonicalQRawUnified.canonical.Q.raw checkedPrefix checkedKernel
  rfl

theorem actual_raw_factor (self rhs : A4) :
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw self rhs =
      actualPrefix actualKernel self rhs := by
  unfold AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw actualPrefix actualKernel
  rfl

private theorem ix0 {A : Type} (a b c d : A) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
private theorem ix1 {A : Type} (a b c d : A) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
private theorem ix2 {A : Type} (a b c d : A) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
private theorem ix3 {A : Type} (a b c d : A) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl

private theorem map_left_four (a b c d : U32) :
    core.array.Array.map
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64
      (Array.make 4#usize [a,b,c,d]) () = .ok (Array.make 4#usize [cv a,cv b,cv c,cv d]) := by
  obtain ⟨mapped,hm⟩ := AspisR1CanonicalQRawUnified.Proof.raw_left_map_total (Array.make 4#usize [a,b,c,d])
  have hv := AspisR1QRawActualC0V2.closure_zero_map_val_local _ mapped hm
  have he : mapped=Array.make 4#usize [cv a,cv b,cv c,cv d] := by
    apply Subtype.ext
    simpa only [Array.make,List.map_cons,List.map_nil] using hv
  exact he ▸ hm
private theorem map_right_four (a b c d : U32) :
    core.array.Array.map
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
      (Array.make 4#usize [a,b,c,d]) () = .ok (Array.make 4#usize [cv a,cv b,cv c,cv d]) := by
  obtain ⟨mapped,hm⟩ := AspisR1CanonicalQRawUnified.Proof.raw_right_map_total (Array.make 4#usize [a,b,c,d])
  have hv := AspisR1QRawActualC0V2.closure_one_map_val_local _ mapped hm
  have he : mapped=Array.make 4#usize [cv a,cv b,cv c,cv d] := by
    apply Subtype.ext
    simpa only [Array.make,List.map_cons,List.map_nil] using hv
  exact he ▸ hm

/-- Only input words are specialized; the checked arithmetic kernel stays sealed. -/
theorem checked_raw_literal_prefix (a b c d e f g h : U32) :
    AspisR1CanonicalQRawUnified.canonical.Q.raw
      (Array.make 4#usize [a,b,c,d]) (Array.make 4#usize [e,f,g,h]) =
      checkedKernel (cv a) (cv b) (cv c) (cv d) (cv e) (cv f) (cv g) (cv h) := by
  rw [checked_raw_factor]
  unfold checkedPrefix
  rw [map_left_four]
  simp only [bind_tc_ok,ix0,ix1,ix2,ix3]
  rw [map_right_four]
  simp only [bind_tc_ok,ix0,ix1,ix2,ix3]

/-- Only actual direct reads/casts are specialized; no arithmetic DAG unfolds. -/
theorem actual_raw_literal_prefix (a b c d e f g h : U32) :
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw
      (Array.make 4#usize [a,b,c,d]) (Array.make 4#usize [e,f,g,h]) =
      actualKernel (cv a) (cv b) (cv c) (cv d) (cv e) (cv f) (cv g) (cv h) := by
  rw [actual_raw_factor]
  unfold actualPrefix
  simp only [bind_tc_ok,ix0,ix1,ix2,ix3,lift]

#print axioms checked_raw_factor
#print axioms actual_raw_factor
#print axioms checked_raw_literal_prefix
#print axioms actual_raw_literal_prefix
end AspisR1S9ActualRawKernelsV1
