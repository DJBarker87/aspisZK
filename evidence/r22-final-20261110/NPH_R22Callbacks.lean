import NPH_R22Producers
import SAQ_Arithmetic
import SAQ_MixedSource
import SAQ_LineQuery
import FIp_CircleSource
import FIp_CircleQuery
import SAQ_Decoder
import Port4C_RowStd

/-! NPH_ (R22, separate limb invariant, step 2): W-lemmas for the wide/extension query
callbacks installed by LIBC_QueryOps.seed and NJJ_QueryOps.concrete. W is limbs ≤ P
(P = 2^31-1), the domain on which NPH_R22Weak/Producers prove the kernels checked-total.
- CurrentWide (CW) tower above QM31: M31.mul (any input, output < P), CM31/QM31/WideExact
  mul_m31 (any input; output limbs < P), WideExact add/sub/mul and mul_u (W to ok W).
- op2 SAQ_Arithmetic.add, op9 SAQ_Arithmetic.mulK: W to ok W.
- op3 SAQ_MixedSource.mulE: W wide operand and ANY QM31 power to ok W (canonicalQ reduces
  the power below P first).
- op1 fromK, op10 fromM (Port4C_RowStd): W preserved (zero limbs).
- op16 SAQ_LineQuery.line, op17 FIp_CircleQuery.circle: W alpha and W values, ANY inverse
  array, to ok W (every inverse lane enters through M31.mul, total on all U32).
- op21 SAQ_Decoder.read: every successful output has all eight limbs < P (strict record
  parser, ExtractedRecordByteCanonicality.slice_success).
The SAQ_WideABI conversions toQ/toW are field-wise copies, so W on the Stage2 carrier is
stated as W of the CW image. No ops interface or merged module is changed. Standard axioms. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Callbacks
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef AspisR1.NPH_R22FieldCopies AspisR1.NPH_R22Weak AspisR1.NPH_R22Producers

abbrev CWW (x : AspisR1CurrentWide.field.wide_exact.WideExact) : Prop := CW_WQ x.c0 ∧ CW_WQ x.c1
/-- W on the Stage2 QM31 carrier (K of SAQ_WideABI), through the field-wise copy toQ. -/
abbrev WK (x : SAQ_WideABI.K) : Prop := CW_WQ (SAQ_WideABI.toQ x)
/-- W on the Stage2 wide carrier (E of SAQ_WideABI), through the field-wise copy toW. -/
abbrev WE (x : SAQ_WideABI.E) : Prop := CWW (SAQ_WideABI.toW x)

/-! ### CurrentWide tower above QM31 -/

theorem CW_M31_mul_lt (x y : U32) :
    ∃ z, AspisR1CurrentWide.field.M31.mul x y = ok z ∧ z.val ≤ 2147483647 := by
  obtain ⟨z, hz, hv⟩ := refMul_total x y
  exact ⟨z, by rw [CW_M31_mul_eq]; exact hz, by omega⟩

theorem CW_CM31_mul_m31_weak (a : AspisR1CurrentWide.field.CM31) (r : U32) :
    ∃ z, AspisR1CurrentWide.field.CM31.mul_m31 a r = ok z ∧ CW_WC z := by
  obtain ⟨m, hm, vm⟩ := CW_M31_mul_lt a.a r
  obtain ⟨m1, hm1, vm1⟩ := CW_M31_mul_lt a.b r
  exact ⟨({ a := m, b := m1 } : AspisR1CurrentWide.field.CM31),
    by simp only [AspisR1CurrentWide.field.CM31.mul_m31, hm, hm1, bind_tc_ok], vm, vm1⟩

theorem CW_QM31_mul_m31_weak (q : AspisR1CurrentWide.field.QM31) (r : U32) :
    ∃ z, AspisR1CurrentWide.field.QM31.mul_m31 q r = ok z ∧ CW_WQ z := by
  obtain ⟨c, hc, vc⟩ := CW_CM31_mul_m31_weak q.c0 r
  obtain ⟨c1, hc1, vc1⟩ := CW_CM31_mul_m31_weak q.c1 r
  exact ⟨({ c0 := c, c1 := c1 } : AspisR1CurrentWide.field.QM31),
    by simp only [AspisR1CurrentWide.field.QM31.mul_m31, hc, hc1, bind_tc_ok], vc, vc1⟩

theorem CW_WideExact_mul_m31_weak (x : AspisR1CurrentWide.field.wide_exact.WideExact) (r : U32) :
    ∃ z, AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 x r = ok z ∧ CWW z := by
  have hPv : (AspisR1CurrentWide.field.P).val = 2147483647 := by unfold AspisR1CurrentWide.field.P; rfl
  obtain ⟨i, hi, _⟩ := WP.spec_imp_exists (UScalar.rem_spec r (y := AspisR1CurrentWide.field.P) (by rw [hPv]; decide))
  obtain ⟨q, hq, vq⟩ := CW_QM31_mul_m31_weak x.c0 i
  obtain ⟨q1, hq1, vq1⟩ := CW_QM31_mul_m31_weak x.c1 i
  exact ⟨({ c0 := q, c1 := q1 } : AspisR1CurrentWide.field.wide_exact.WideExact),
    by simp only [AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31, hi, hq, hq1, bind_tc_ok], vq, vq1⟩

theorem CW_WideExact_add_weak (x y : AspisR1CurrentWide.field.wide_exact.WideExact) (hx : CWW x) (hy : CWW y) :
    ∃ z, AspisR1CurrentWide.field.wide_exact.WideExact.add x y = ok z ∧ CWW z := by
  obtain ⟨q, hq, vq⟩ := CW_QM31_add_weak x.c0 y.c0 hx.1 hy.1
  obtain ⟨q1, hq1, vq1⟩ := CW_QM31_add_weak x.c1 y.c1 hx.2 hy.2
  exact ⟨({ c0 := q, c1 := q1 } : AspisR1CurrentWide.field.wide_exact.WideExact),
    by simp only [AspisR1CurrentWide.field.wide_exact.WideExact.add, hq, hq1, bind_tc_ok], vq, vq1⟩

theorem CW_WideExact_sub_weak (x y : AspisR1CurrentWide.field.wide_exact.WideExact) (hx : CWW x) (hy : CWW y) :
    ∃ z, AspisR1CurrentWide.field.wide_exact.WideExact.sub x y = ok z ∧ CWW z := by
  obtain ⟨q, hq, vq⟩ := CW_QM31_sub_weak x.c0 y.c0 hx.1 hy.1
  obtain ⟨q1, hq1, vq1⟩ := CW_QM31_sub_weak x.c1 y.c1 hx.2 hy.2
  exact ⟨({ c0 := q, c1 := q1 } : AspisR1CurrentWide.field.wide_exact.WideExact),
    by simp only [AspisR1CurrentWide.field.wide_exact.WideExact.sub, hq, hq1, bind_tc_ok], vq, vq1⟩

theorem CW_mul_u_weak (q : AspisR1CurrentWide.field.QM31) (hq : CW_WQ q) :
    ∃ z, AspisR1CurrentWide.field.wide_exact.mul_u q = ok z ∧ CW_WQ z := by
  obtain ⟨c, hc, vc⟩ := CW_mul_by_r_weak q.c1 hq.2
  exact ⟨({ c0 := c, c1 := q.c0 } : AspisR1CurrentWide.field.QM31),
    by simp only [AspisR1CurrentWide.field.wide_exact.mul_u, hc, bind_tc_ok], vc, hq.1⟩

theorem CW_WideExact_mul_weak (x y : AspisR1CurrentWide.field.wide_exact.WideExact) (hx : CWW x) (hy : CWW y) :
    ∃ z, AspisR1CurrentWide.field.wide_exact.WideExact.mul x y = ok z ∧ CWW z := by
  obtain ⟨ac, hac, vac⟩ := CW_QM31_mul_weak x.c0 y.c0 hx.1 hy.1
  obtain ⟨bd, hbd, vbd⟩ := CW_QM31_mul_weak x.c1 y.c1 hx.2 hy.2
  obtain ⟨q, hq, vq⟩ := CW_QM31_add_weak x.c0 x.c1 hx.1 hx.2
  obtain ⟨q1, hq1, vq1⟩ := CW_QM31_add_weak y.c0 y.c1 hy.1 hy.2
  obtain ⟨cr, hcr, vcr⟩ := CW_QM31_mul_weak q q1 vq vq1
  obtain ⟨q2, hq2, vq2⟩ := CW_mul_u_weak bd vbd
  obtain ⟨q3, hq3, vq3⟩ := CW_QM31_add_weak ac q2 vac vq2
  obtain ⟨q4, hq4, vq4⟩ := CW_QM31_sub_weak cr ac vcr vac
  obtain ⟨q5, hq5, vq5⟩ := CW_QM31_sub_weak q4 bd vq4 vbd
  exact ⟨({ c0 := q3, c1 := q5 } : AspisR1CurrentWide.field.wide_exact.WideExact),
    by simp only [AspisR1CurrentWide.field.wide_exact.WideExact.mul, hac, hbd, hq, hq1, hcr, hq2, hq3, hq4, hq5, bind_tc_ok],
    vq3, vq5⟩

/-! ### op2, op9: SAQ_Arithmetic -/

theorem SAQ_Arithmetic_add_W (x y : SAQ_WideABI.E) (hx : WE x) (hy : WE y) :
    ∃ z, SAQ_Arithmetic.add x y = ok z ∧ WE z := by
  obtain ⟨w, hw, vw⟩ := CW_WideExact_add_weak (SAQ_WideABI.toW x) (SAQ_WideABI.toW y) hx hy
  exact ⟨SAQ_WideABI.fromW w, by simp only [SAQ_Arithmetic.add, hw, bind_tc_ok], vw⟩

theorem SAQ_Arithmetic_mulK_W (x y : SAQ_WideABI.K) (hx : WK x) (hy : WK y) :
    ∃ z, SAQ_Arithmetic.mulK x y = ok z ∧ WK z := by
  obtain ⟨w, hw, vw⟩ := CW_QM31_mul_weak (SAQ_WideABI.toQ x) (SAQ_WideABI.toQ y) hx hy
  exact ⟨SAQ_WideABI.fromQ w, by simp only [SAQ_Arithmetic.mulK, hw, bind_tc_ok], vw⟩

/-! ### op3: SAQ_MixedSource.mulE -/

theorem remP_lt (x : U32) : ∃ z, (x % (2147483647#u32) : Result U32) = ok z ∧ z.val ≤ 2147483647 := by
  obtain ⟨out, run, value⟩ := WP.spec_imp_exists (UScalar.rem_spec x (y := 2147483647#u32) (by decide))
  refine ⟨out, run, ?_⟩
  rw [value]
  exact Nat.le_of_lt (Nat.mod_lt _ (by decide))

theorem SAQ_MixedSource_canonicalQ_W (q : SAQ_WideABI.Q) :
    ∃ r, SAQ_MixedSource.canonicalQ q = ok r ∧ CW_WQ r := by
  obtain ⟨a, ha, va⟩ := remP_lt q.c0.a
  obtain ⟨b, hb, vb⟩ := remP_lt q.c0.b
  obtain ⟨c, hc, vc⟩ := remP_lt q.c1.a
  obtain ⟨d, hd, vd⟩ := remP_lt q.c1.b
  exact ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, by simp only [SAQ_MixedSource.canonicalQ, ha, hb, hc, hd, bind_tc_ok],
    ⟨va, vb⟩, ⟨vc, vd⟩⟩

theorem SAQ_MixedSource_source_W (x : SAQ_WideABI.W) (q : SAQ_WideABI.Q) (hx : CWW x) :
    ∃ z, SAQ_MixedSource.source x q = ok z ∧ CWW z := by
  obtain ⟨r, hr, vr⟩ := SAQ_MixedSource_canonicalQ_W q
  obtain ⟨a, ha, va⟩ := CW_QM31_mul_weak x.c0 r hx.1 vr
  obtain ⟨b, hb, vb⟩ := CW_QM31_mul_weak x.c1 r hx.2 vr
  exact ⟨⟨a, b⟩, by simp only [SAQ_MixedSource.source, hr, ha, hb, bind_tc_ok], va, vb⟩

theorem SAQ_MixedSource_mulE_W (x : SAQ_WideABI.E) (q : SAQ_WideABI.K) (hx : WE x) :
    ∃ z, SAQ_MixedSource.mulE x q = ok z ∧ WE z := by
  obtain ⟨w, hw, vw⟩ := SAQ_MixedSource_source_W (SAQ_WideABI.toW x) (SAQ_WideABI.toQ q) hx
  exact ⟨SAQ_WideABI.fromW w, by simp only [SAQ_MixedSource.mulE, hw, bind_tc_ok], vw⟩

/-! ### op1, op10: Port4C_RowStd embeddings -/

theorem zero_W : (0#u32 : U32).val ≤ 2147483647 := by first | decide | simp

theorem RowStd_fromK_W (q : SAQ_WideABI.K) (hq : WK q) : WE (Port4C_RowStd.fromK q) :=
  ⟨hq, ⟨zero_W, zero_W⟩, ⟨zero_W, zero_W⟩⟩

theorem RowStd_fromM_W (m : U32) (hm : m.val ≤ 2147483647) : WE (Port4C_RowStd.fromM m) :=
  ⟨⟨⟨hm, zero_W⟩, ⟨zero_W, zero_W⟩⟩, ⟨zero_W, zero_W⟩, ⟨zero_W, zero_W⟩⟩

/-! ### op16: line fold -/

theorem LineSource_line_W (alpha a b c d : AspisR1CurrentWide.field.wide_exact.WideExact) (ix iy lx ly lz : U32)
    (hα : CWW alpha) (ha : CWW a) (hb : CWW b) (hc : CWW c) (hd : CWW d) :
    ∃ z, SAQ_LineSource.line alpha (Array.make 4#usize [a,b,c,d]) (Array.make 5#usize [ix,iy,lx,ly,lz]) = ok z ∧ CWW z := by
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
  have ii2 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 2#usize = .ok lx := rfl
  have ii3 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 3#usize = .ok ly := rfl
  have ii4 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 4#usize = .ok lz := rfl
  obtain ⟨we, e1, w1⟩ := CW_WideExact_add_weak a b ha hb
  obtain ⟨we1, e2, w2⟩ := CW_WideExact_add_weak we c w1 hc
  obtain ⟨we2, e3, w3⟩ := CW_WideExact_add_weak we1 d w2 hd
  obtain ⟨g0, e4, w4⟩ := CW_WideExact_mul_m31_weak we2 SAQ_LineSource.quarter
  obtain ⟨we3, e5, w5⟩ := CW_WideExact_sub_weak we c w1 hc
  obtain ⟨we4, e6, w6⟩ := CW_WideExact_sub_weak we3 d w5 hd
  obtain ⟨m, e7, _⟩ := CW_M31_mul_lt SAQ_LineSource.quarter lz
  obtain ⟨g2, e8, w8⟩ := CW_WideExact_mul_m31_weak we4 m
  obtain ⟨we5, e9, w9⟩ := CW_WideExact_sub_weak a b ha hb
  obtain ⟨m1, e10, _⟩ := CW_M31_mul_lt 1073741824#u32 lx
  obtain ⟨k0, e11, w11⟩ := CW_WideExact_mul_m31_weak we5 m1
  obtain ⟨we6, e12, w12⟩ := CW_WideExact_sub_weak d c hd hc
  obtain ⟨m2, e13, _⟩ := CW_M31_mul_lt 1073741824#u32 ly
  obtain ⟨k1, e14, w14⟩ := CW_WideExact_mul_m31_weak we6 m2
  obtain ⟨we7, e15, w15⟩ := CW_WideExact_add_weak k0 k1 w11 w14
  obtain ⟨g1, e16, w16⟩ := CW_WideExact_mul_m31_weak we7 1073741824#u32
  obtain ⟨we8, e17, w17⟩ := CW_WideExact_sub_weak k0 k1 w11 w14
  obtain ⟨m3, e18, _⟩ := CW_M31_mul_lt 1073741824#u32 lz
  obtain ⟨g3, e19, w19⟩ := CW_WideExact_mul_m31_weak we8 m3
  obtain ⟨we9, e20, w20⟩ := CW_WideExact_mul_weak alpha g3 hα w19
  obtain ⟨we10, e21, w21⟩ := CW_WideExact_add_weak g2 we9 w8 w20
  obtain ⟨we11, e22, w22⟩ := CW_WideExact_mul_weak alpha we10 hα w21
  obtain ⟨we12, e23, w23⟩ := CW_WideExact_add_weak g1 we11 w16 w22
  obtain ⟨we13, e24, w24⟩ := CW_WideExact_mul_weak alpha we12 hα w23
  obtain ⟨z, e25, w25⟩ := CW_WideExact_add_weak g0 we13 w4 w24
  exact ⟨z, by simp only [SAQ_LineSource.line, ia0, ia1, ia2, ia3, ii2, ii3, ii4, e1, e2, e3, e4, e5, e6, e7, e8, e9,
    e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, bind_tc_ok], w25⟩

theorem SAQ_LineQuery_line_W (alpha : SAQ_WideABI.E) (v : Array SAQ_WideABI.E 4#usize) (inverse : Array U32 5#usize)
    (hα : WE alpha) (hv : ∀ x ∈ v.val, WE x) :
    ∃ z, SAQ_LineQuery.line alpha v inverse = ok z ∧ WE z := by
  obtain ⟨a, b, c, d, rfl⟩ := SAQ_LineArrays.four v
  obtain ⟨ix, iy, lx, ly, lz, rfl⟩ := SAQ_LineArrays.five inverse
  have ha := hv a (List.Mem.head _)
  have hb := hv b (List.Mem.tail _ (List.Mem.head _))
  have hc := hv c (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hd := hv d (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hvals : SAQ_LineQuery.toValues (Array.make 4#usize [a,b,c,d]) =
      Array.make 4#usize [SAQ_WideABI.toW a, SAQ_WideABI.toW b, SAQ_WideABI.toW c, SAQ_WideABI.toW d] := rfl
  obtain ⟨w, hw, vw⟩ := LineSource_line_W (SAQ_WideABI.toW alpha) (SAQ_WideABI.toW a) (SAQ_WideABI.toW b)
    (SAQ_WideABI.toW c) (SAQ_WideABI.toW d) ix iy lx ly lz hα ha hb hc hd
  exact ⟨SAQ_WideABI.fromW w, by simp only [SAQ_LineQuery.line, hvals, hw, bind_tc_ok], vw⟩

/-! ### op17: circle fold -/

theorem CircleSource_circle_W (alpha a b c d : AspisR1CurrentWide.field.wide_exact.WideExact) (ix iy lx ly lz : U32)
    (hα : CWW alpha) (ha : CWW a) (hb : CWW b) (hc : CWW c) (hd : CWW d) :
    ∃ z, FIp_CircleSource.circle alpha (Array.make 4#usize [a,b,c,d]) (Array.make 5#usize [ix,iy,lx,ly,lz]) = ok z ∧ CWW z := by
  have ia0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
  have ia1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
  have ia2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
  have ia3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
  have ii0 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 0#usize = .ok ix := rfl
  have ii1 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 1#usize = .ok iy := rfl
  obtain ⟨we, e1, w1⟩ := CW_WideExact_add_weak a b ha hb
  obtain ⟨we1, e2, w2⟩ := CW_WideExact_add_weak we c w1 hc
  obtain ⟨we2, e3, w3⟩ := CW_WideExact_add_weak we1 d w2 hd
  obtain ⟨g0, e4, w4⟩ := CW_WideExact_mul_m31_weak we2 SAQ_LineSource.quarter
  obtain ⟨we3, e5, w5⟩ := CW_WideExact_sub_weak a b ha hb
  obtain ⟨we4, e6, w6⟩ := CW_WideExact_sub_weak we3 c w5 hc
  obtain ⟨we5, e7, w7⟩ := CW_WideExact_add_weak we4 d w6 hd
  obtain ⟨m, e8, _⟩ := CW_M31_mul_lt SAQ_LineSource.quarter iy
  obtain ⟨g1, e9, w9⟩ := CW_WideExact_mul_m31_weak we5 m
  obtain ⟨we6, e10, w10⟩ := CW_WideExact_sub_weak we c w1 hc
  obtain ⟨we7, e11, w11⟩ := CW_WideExact_sub_weak we6 d w10 hd
  obtain ⟨m1, e12, _⟩ := CW_M31_mul_lt SAQ_LineSource.quarter ix
  obtain ⟨g2, e13, w13⟩ := CW_WideExact_mul_m31_weak we7 m1
  obtain ⟨we8, e14, w14⟩ := CW_WideExact_add_weak we3 c w5 hc
  obtain ⟨we9, e15, w15⟩ := CW_WideExact_sub_weak we8 d w14 hd
  obtain ⟨m2, e16, _⟩ := CW_M31_mul_lt m1 iy
  obtain ⟨g3, e17, w17⟩ := CW_WideExact_mul_m31_weak we9 m2
  obtain ⟨we10, e18, w18⟩ := CW_WideExact_mul_weak alpha g3 hα w17
  obtain ⟨we11, e19, w19⟩ := CW_WideExact_add_weak g2 we10 w13 w18
  obtain ⟨we12, e20, w20⟩ := CW_WideExact_mul_weak alpha we11 hα w19
  obtain ⟨we13, e21, w21⟩ := CW_WideExact_add_weak g1 we12 w9 w20
  obtain ⟨we14, e22, w22⟩ := CW_WideExact_mul_weak alpha we13 hα w21
  obtain ⟨z, e23, w23⟩ := CW_WideExact_add_weak g0 we14 w4 w22
  exact ⟨z, by simp only [FIp_CircleSource.circle, ia0, ia1, ia2, ia3, ii0, ii1, e1, e2, e3, e4, e5, e6, e7, e8, e9,
    e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, bind_tc_ok], w23⟩

theorem FIp_CircleQuery_circle_W (alpha : SAQ_WideABI.E) (v : Array SAQ_WideABI.E 4#usize) (inverse : Array U32 5#usize)
    (hα : WE alpha) (hv : ∀ x ∈ v.val, WE x) :
    ∃ z, FIp_CircleQuery.circle alpha v inverse = ok z ∧ WE z := by
  obtain ⟨a, b, c, d, rfl⟩ := SAQ_LineArrays.four v
  obtain ⟨ix, iy, lx, ly, lz, rfl⟩ := SAQ_LineArrays.five inverse
  have ha := hv a (List.Mem.head _)
  have hb := hv b (List.Mem.tail _ (List.Mem.head _))
  have hc := hv c (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hd := hv d (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have hvals : FIp_CircleQuery.toValues (Array.make 4#usize [a,b,c,d]) =
      Array.make 4#usize [SAQ_WideABI.toW a, SAQ_WideABI.toW b, SAQ_WideABI.toW c, SAQ_WideABI.toW d] := rfl
  obtain ⟨w, hw, vw⟩ := CircleSource_circle_W (SAQ_WideABI.toW alpha) (SAQ_WideABI.toW a) (SAQ_WideABI.toW b)
    (SAQ_WideABI.toW c) (SAQ_WideABI.toW d) ix iy lx ly lz hα ha hb hc hd
  exact ⟨SAQ_WideABI.fromW w, by simp only [FIp_CircleQuery.circle, hvals, hw, bind_tc_ok], vw⟩

/-! ### op21: record decoder (producer: limbs < P on success) -/

theorem SAQ_Decoder_read_lt (bytes : Slice U8) (i : Usize) (z : SAQ_WideABI.E)
    (run : SAQ_Decoder.read bytes i = ok z) :
    (SAQ_WideABI.toW z).c0.c0.a.val < 2147483647 ∧ (SAQ_WideABI.toW z).c0.c0.b.val < 2147483647 ∧
    (SAQ_WideABI.toW z).c0.c1.a.val < 2147483647 ∧ (SAQ_WideABI.toW z).c0.c1.b.val < 2147483647 ∧
    (SAQ_WideABI.toW z).c1.c0.a.val < 2147483647 ∧ (SAQ_WideABI.toW z).c1.c0.b.val < 2147483647 ∧
    (SAQ_WideABI.toW z).c1.c1.a.val < 2147483647 ∧ (SAQ_WideABI.toW z).c1.c1.b.val < 2147483647 := by
  unfold SAQ_Decoder.read at run
  obtain ⟨start, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨finish, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨selected, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨decoded, hd, run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases decoded with
  | none => simp [core.option.Option.unwrap] at run
  | some raw =>
    simp only [core.option.Option.unwrap, bind_tc_ok] at run
    have same : SAQ_RecordDecode.fromRecord raw = z := Result.ok.inj run
    subst z
    obtain ⟨_, arr, _, hc, hp⟩ := ExtractedRecordByteCanonicality.slice_success selected raw hd
    subst hp
    exact ⟨hc 0, hc 1, hc 2, hc 3, hc 4, hc 5, hc 6, hc 7⟩

theorem SAQ_Decoder_read_W (bytes : Slice U8) (i : Usize) (z : SAQ_WideABI.E)
    (run : SAQ_Decoder.read bytes i = ok z) : WE z := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := SAQ_Decoder_read_lt bytes i z run
  exact ⟨⟨⟨Nat.le_of_lt h0, Nat.le_of_lt h1⟩, ⟨Nat.le_of_lt h2, Nat.le_of_lt h3⟩⟩,
    ⟨⟨Nat.le_of_lt h4, Nat.le_of_lt h5⟩, ⟨Nat.le_of_lt h6, Nat.le_of_lt h7⟩⟩⟩

#print axioms CW_M31_mul_lt
#print axioms CW_CM31_mul_m31_weak
#print axioms CW_QM31_mul_m31_weak
#print axioms CW_WideExact_mul_m31_weak
#print axioms CW_WideExact_add_weak
#print axioms CW_WideExact_sub_weak
#print axioms CW_mul_u_weak
#print axioms CW_WideExact_mul_weak
#print axioms SAQ_Arithmetic_add_W
#print axioms SAQ_Arithmetic_mulK_W
#print axioms remP_lt
#print axioms SAQ_MixedSource_canonicalQ_W
#print axioms SAQ_MixedSource_source_W
#print axioms SAQ_MixedSource_mulE_W
#print axioms zero_W
#print axioms RowStd_fromK_W
#print axioms RowStd_fromM_W
#print axioms LineSource_line_W
#print axioms SAQ_LineQuery_line_W
#print axioms CircleSource_circle_W
#print axioms FIp_CircleQuery_circle_W
#print axioms SAQ_Decoder_read_lt
#print axioms SAQ_Decoder_read_W
end AspisR1.NPH_R22Callbacks
