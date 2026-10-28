import LPi_TowerValues
import LPf_WideConstruction
import AspisR1Post25Sampler.Funs
set_option autoImplicit false
noncomputable section
namespace NBG_WideCarriers
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem wide_add (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.add x y = ok z ∧
      canonE z ∧ ew z = (addQ (qw x.c0) (qw y.c0), addQ (qw x.c1) (qw y.c1)) := by
  obtain ⟨a,ha,ca,va⟩ := LPi_TowerValues.qm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := LPi_TowerValues.qm_add x.c1 y.c1 hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,
    ha,hb,bind_tc_ok],⟨ca,cb⟩,Prod.ext va vb⟩

theorem limbs_result (a b c d e f g h : U32) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [a,b,c,d,e,f,g,h]) =
      ok (if a < 2147483647#u32 ∧ b < 2147483647#u32 ∧ c < 2147483647#u32 ∧
        d < 2147483647#u32 ∧ e < 2147483647#u32 ∧ f < 2147483647#u32 ∧
        g < 2147483647#u32 ∧ h < 2147483647#u32
        then some (LPf_WideConstruction.value a b c d e f g h) else none) := by
  simp [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
    Array.index_usize,Array.make,FIo_Native.aspis_core.field.P,LPf_WideConstruction.value]
  repeat' split
  all_goals simp_all

theorem to_limbs_result (x : NE) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x =
      ok (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
        x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) := rfl

/-- Wrong lengths reject before any byte index, for arbitrary machine slices. -/
theorem wrong_byte_length (bytes : Slice U8) (h : bytes.val.length ≠ 32) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes = ok none := by
  have hn : Slice.len bytes != 32#usize := by
    simp only [bne_iff_ne]
    intro eq
    have values := congrArg UScalar.val eq
    apply h
    change bytes.val.length = 32 at values
    exact values
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,hn,if_true]

abbrev PQ := AspisR1Post25Sampler.field.QM31
abbrev PE := AspisR1Post25Sampler.field.WideExact
def pw (x : PQ) : Nat × Nat × Nat × Nat :=
  (x.c0.a.val,x.c0.b.val,x.c1.a.val,x.c1.b.val)
def reduced (x : PQ) : Nat × Nat × Nat × Nat :=
  (x.c0.a.val%2147483647,x.c0.b.val%2147483647,
   x.c1.a.val%2147483647,x.c1.b.val%2147483647)

theorem remainder (x : U32) : ∃ z, x % 2147483647#u32 = ok z ∧
    z.val = x.val % 2147483647 :=
  WP.spec_imp_exists (UScalar.rem_spec x (y:=2147483647#u32) (by decide))

theorem canonical_qm31 (x : PQ) : ∃ z,
    AspisR1Post25Sampler.field.canonical_qm31 x = ok z ∧ pw z = reduced x := by
  obtain ⟨a,ha,va⟩ := remainder x.c0.a
  obtain ⟨b,hb,vb⟩ := remainder x.c0.b
  obtain ⟨c,hc,vc⟩ := remainder x.c1.a
  obtain ⟨d,hd,vd⟩ := remainder x.c1.b
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,Prod.ext va (Prod.ext vb (Prod.ext vc vd))⟩
  simp only [AspisR1Post25Sampler.field.canonical_qm31,
    AspisR1Post25Sampler.field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    AspisR1Post25Sampler.field.P,ha,hb,hc,hd,bind_tc_ok]

theorem wide_new (x y : PQ) : ∃ z : PE,
    AspisR1Post25Sampler.field.WideExact.new x y = ok z ∧
      (pw z.c0,pw z.c1) = (reduced x,reduced y) := by
  obtain ⟨a,ha,va⟩ := canonical_qm31 x
  obtain ⟨b,hb,vb⟩ := canonical_qm31 y
  exact ⟨⟨a,b⟩,by simp only [AspisR1Post25Sampler.field.WideExact.new,ha,hb,bind_tc_ok],
    Prod.ext va vb⟩

#print axioms wide_add
#print axioms limbs_result
#print axioms to_limbs_result
#print axioms wrong_byte_length
#print axioms remainder
#print axioms canonical_qm31
#print axioms wide_new
end NBG_WideCarriers
