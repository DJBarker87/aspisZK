import NEI_FieldWide
import NEB_AdditiveCalls
import NEB_NativeFieldScalars
import FIo_M31Bridge
import FIo_M31SubBridge
import FIo_M31MulBridge
import NEI_LineDomains
set_option autoImplicit false
noncomputable section
namespace NEI_ReleaseField
open Aeneas Aeneas.Std Result AspisR1
open FIo_FieldBridge (NC NQ NE cm qm wide map)
open LPi_FieldValues (canonC canonQ canonE)
namespace C
abbrev M := AspisR1CurrentWide.field.M31
abbrev F := AspisR1CurrentWide.field.CM31
end C

theorem transport {A B : Type} (f : A → B) (r : Result A) (s : Result B) (z : A)
    (same : map f r = s) (run : r = ok z) : s = ok (f z) := by
  rw [← same,run]
  rfl

theorem m_add (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    FIo_Native.aspis_core.field.M31.add x y = AspisR1CurrentWide.field.M31.add x y :=
  FIo_M31Bridge.add x y hx hy

theorem m_sub (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    FIo_Native.aspis_core.field.M31.sub x y = AspisR1CurrentWide.field.M31.sub x y :=
  FIo_M31SubBridge.sub x y hx hy

theorem m_mul (x y : U32) :
    FIo_Native.aspis_core.field.M31.mul x y = AspisR1CurrentWide.field.M31.mul x y :=
  FIo_M31MulBridge.same x y

theorem reduce (x : U64) :
    FIo_Native.aspis_core.field.reduce_u64 x = AspisR1CurrentWide.field.reduce_u64 x :=
  FIo_ReduceBridge.same x

theorem m_reduce (x : U64) :
    FIo_Native.aspis_core.field.M31.reduce_u64 x = AspisR1CurrentWide.field.M31.reduce_u64 x := by
  simp only [FIo_Native.aspis_core.field.M31.reduce_u64,
    AspisR1CurrentWide.field.M31.reduce_u64,reduce]

theorem m_double (x : U32) (hx : x.val < 2147483647) :
    FIo_Native.aspis_core.field.M31.double x = AspisR1CurrentWide.field.M31.double x := by
  simp only [FIo_Native.aspis_core.field.M31.double,
    AspisR1CurrentWide.field.M31.double,m_add x x hx hx]

theorem cm_add (x y : NC) (hx : canonC x) (hy : canonC y) :
    map cm (FIo_Native.aspis_core.field.CM31.add x y) =
      AspisR1CurrentWide.field.CM31.add (cm x) (cm y) := by
  obtain ⟨a,b,ha,hb,ca,cb,hz⟩ := NEB_FieldDomains.cm_add_calls x y hx hy
  rw [hz]
  simp only [map,cm,AspisR1CurrentWide.field.CM31.add]
  rw [← m_add x.a y.a hx.1 hy.1,ha]
  simp only [bind_tc_ok]
  rw [← m_add x.b y.b hx.2 hy.2,hb]
  rfl

theorem cm_sub (x y : NC) (hx : canonC x) (hy : canonC y) :
    map cm (FIo_Native.aspis_core.field.CM31.sub x y) =
      AspisR1CurrentWide.field.CM31.sub (cm x) (cm y) := by
  obtain ⟨a,b,ha,hb,ca,cb,hz⟩ := NEB_FieldDomains.cm_sub_calls x y hx hy
  rw [hz]
  simp only [map,cm,AspisR1CurrentWide.field.CM31.sub]
  rw [← m_sub x.a y.a hx.1 hy.1,ha]
  simp only [bind_tc_ok]
  rw [← m_sub x.b y.b hx.2 hy.2,hb]
  rfl

theorem cm_scale (x : NC) (s : U32) :
    map cm (FIo_Native.aspis_core.field.CM31.mul_m31 x s) =
      AspisR1CurrentWide.field.CM31.mul_m31 (cm x) s := by
  obtain ⟨a,b,ha,ca,hb,cb,hz⟩ := NEB_CMCalls.scale x s
  rw [hz]
  simp only [map,cm,AspisR1CurrentWide.field.CM31.mul_m31,← m_mul,ha,hb,bind_tc_ok]

theorem cm_mul (x y : NC) (hx : canonC x) (hy : canonC y) :
    map cm (FIo_Native.aspis_core.field.CM31.mul x y) =
      AspisR1CurrentWide.field.CM31.mul (cm x) (cm y) := by
  obtain ⟨m0,m1,m2,a,b,c,h0,c0,h1,c1,h2,c2,v2,ha,ca,hb,cb,hc,cc,hz⟩ := NEB_CMCalls.multiply x y hx hy
  have hp : LPi_CMProduct.sum x * LPi_CMProduct.sum y = ok (LPi_CMProduct.cross x y) := by
    have h := NEB_NativeFieldScalars.cross_checked x y hx hy
    simpa only [NEB_NativeFieldScalars.sum_checked,bind_tc_ok] using h
  rw [hz]
  simp only [map,cm,AspisR1CurrentWide.field.CM31.mul,← m_mul,h0,h1,bind_tc_ok,
    NEB_NativeFieldScalars.sum_checked,hp,← m_reduce,h2]
  rw [← m_sub m0 m1 c0 c1,ha]
  simp only [bind_tc_ok]
  rw [← m_sub m2 m0 c2 c0,hb]
  simp only [bind_tc_ok]
  rw [← m_sub b m1 cb c1,hc]
  rfl

theorem by_r (x : NC) (hx : canonC x) :
    map cm (FIo_Native.aspis_core.field.mul_by_r x) =
      AspisR1CurrentWide.field.mul_by_r (cm x) := by
  obtain ⟨da,re,db,im,ha,ca,hr,cr,hb,cb,hi,ci,hz⟩ := NEB_ByRCalls.source x hx
  rw [hz]
  simp only [map,cm,AspisR1CurrentWide.field.mul_by_r]
  rw [← m_double x.a hx.1,ha]
  simp only [bind_tc_ok]
  rw [← m_sub da x.b ca hx.2,hr]
  simp only [bind_tc_ok]
  rw [← m_double x.b hx.2,hb]
  simp only [bind_tc_ok]
  rw [← m_add x.a db hx.1 cb,hi]
  rfl

theorem qm_add (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    map qm (FIo_Native.aspis_core.field.QM31.add x y) =
      AspisR1CurrentWide.field.QM31.add (qm x) (qm y) := by
  obtain ⟨a,b,ha,ca,hb,cb,hz⟩ := NEB_QMCalls.add x y hx hy
  have aa := transport cm _ _ a (cm_add x.c0 y.c0 hx.1 hy.1) ha
  have bb := transport cm _ _ b (cm_add x.c1 y.c1 hx.2 hy.2) hb
  rw [hz]
  simp only [map,qm,AspisR1CurrentWide.field.QM31.add,aa,bb,bind_tc_ok]

theorem qm_sub (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    map qm (FIo_Native.aspis_core.field.QM31.sub x y) =
      AspisR1CurrentWide.field.QM31.sub (qm x) (qm y) := by
  obtain ⟨a,b,ha,ca,hb,cb,hz⟩ := NEB_QMCalls.sub x y hx hy
  have aa := transport cm _ _ a (cm_sub x.c0 y.c0 hx.1 hy.1) ha
  have bb := transport cm _ _ b (cm_sub x.c1 y.c1 hx.2 hy.2) hb
  rw [hz]
  simp only [map,qm,AspisR1CurrentWide.field.QM31.sub,aa,bb,bind_tc_ok]

theorem qm_scale (x : NQ) (s : U32) :
    map qm (FIo_Native.aspis_core.field.QM31.mul_m31 x s) =
      AspisR1CurrentWide.field.QM31.mul_m31 (qm x) s := by
  obtain ⟨a,b,ha,ca,hb,cb,hz⟩ := NEB_AdditiveCalls.qm_scale x s
  have aa := transport cm _ _ a (cm_scale x.c0 s) ha
  have bb := transport cm _ _ b (cm_scale x.c1 s) hb
  rw [hz]
  simp only [map,qm,AspisR1CurrentWide.field.QM31.mul_m31,aa,bb,bind_tc_ok]

theorem qm_mul (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    map qm (FIo_Native.aspis_core.field.QM31.mul x y) =
      AspisR1CurrentWide.field.QM31.mul (qm x) (qm y) := by
  obtain ⟨ac,bd,a,b,cross,r,lo,diff,hi,hac,cac,hbd,cbd,ha,ca,hb,cb,hcross,ccross,hr,cr,hlo,clo,hdiff,cdiff,hhi,chi,hz⟩ := NEB_QMCalls.multiply x y hx hy
  have h1 := transport cm _ _ ac (cm_mul x.c0 y.c0 hx.1 hy.1) hac
  have h2 := transport cm _ _ bd (cm_mul x.c1 y.c1 hx.2 hy.2) hbd
  have h3 := transport cm _ _ a (cm_add x.c0 x.c1 hx.1 hx.2) ha
  have h4 := transport cm _ _ b (cm_add y.c0 y.c1 hy.1 hy.2) hb
  have h5 := transport cm _ _ cross (cm_mul a b ca cb) hcross
  have h6 := transport cm _ _ r (by_r bd cbd) hr
  have h7 := transport cm _ _ lo (cm_add ac r cac cr) hlo
  have h8 := transport cm _ _ diff (cm_sub cross ac ccross cac) hdiff
  have h9 := transport cm _ _ hi (cm_sub diff bd cdiff cbd) hhi
  rw [hz]
  simp only [map,qm,AspisR1CurrentWide.field.QM31.mul,h1,h2,h3,h4,h5,h6,h7,h8,h9,bind_tc_ok]

theorem mul_u (x : NQ) (hx : canonQ x) :
    map qm (FIo_Native.aspis_core.field.wide_exact.mul_u x) =
      AspisR1CurrentWide.field.wide_exact.mul_u (qm x) := by
  obtain ⟨_,r,hr,cr,hz,cz⟩ := NEB_ByRCalls.mul_u x hx
  have rr := transport cm _ _ r (by_r x.c1 hx.2) hr
  rw [hz]
  simp only [map,qm,AspisR1CurrentWide.field.wide_exact.mul_u,rr,bind_tc_ok]

theorem wide_add (x y : NE) (hx : canonE x) (hy : canonE y) :
    map wide (FIo_Native.aspis_core.field.wide_exact.WideExact.add x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.add (wide x) (wide y) := by
  obtain ⟨a,b,ha,ca,hb,cb,hz⟩ := NEB_AdditiveCalls.wide_add x y hx hy
  have aa := transport qm _ _ a (qm_add x.c0 y.c0 hx.1 hy.1) ha
  have bb := transport qm _ _ b (qm_add x.c1 y.c1 hx.2 hy.2) hb
  rw [hz]
  simp only [map,wide,AspisR1CurrentWide.field.wide_exact.WideExact.add,aa,bb,bind_tc_ok]

theorem wide_sub (x y : NE) (hx : canonE x) (hy : canonE y) :
    map wide (FIo_Native.aspis_core.field.wide_exact.WideExact.sub x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.sub (wide x) (wide y) := by
  obtain ⟨a,ha,ca,_⟩ := LPi_TowerValues.qm_sub x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,_⟩ := LPi_TowerValues.qm_sub x.c1 y.c1 hx.2 hy.2
  have aa := transport qm _ _ a (qm_sub x.c0 y.c0 hx.1 hy.1) ha
  have bb := transport qm _ _ b (qm_sub x.c1 y.c1 hx.2 hy.2) hb
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.sub,ha,hb,bind_tc_ok,map,wide,
    AspisR1CurrentWide.field.wide_exact.WideExact.sub,aa,bb]
  rfl

theorem wide_mul (x y : NE) (hx : canonE x) (hy : canonE y) :
    map wide (FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul (wide x) (wide y) := by
  obtain ⟨ac,bd,a,b,cross,r,lo,diff,hi,hac,cac,hbd,cbd,ha,ca,hb,cb,hcross,ccross,hr,cr,hlo,clo,hdiff,cdiff,hhi,chi,hz⟩ := NEB_WideCalls.multiply x y hx hy
  have h1 := transport qm _ _ ac (qm_mul x.c0 y.c0 hx.1 hy.1) hac
  have h2 := transport qm _ _ bd (qm_mul x.c1 y.c1 hx.2 hy.2) hbd
  have h3 := transport qm _ _ a (qm_add x.c0 x.c1 hx.1 hx.2) ha
  have h4 := transport qm _ _ b (qm_add y.c0 y.c1 hy.1 hy.2) hb
  have h5 := transport qm _ _ cross (qm_mul a b ca cb) hcross
  have h6 := transport qm _ _ r (mul_u bd cbd) hr
  have h7 := transport qm _ _ lo (qm_add ac r cac cr) hlo
  have h8 := transport qm _ _ diff (qm_sub cross ac ccross cac) hdiff
  have h9 := transport qm _ _ hi (qm_sub diff bd cdiff cbd) hhi
  rw [hz]
  simp only [map,wide,AspisR1CurrentWide.field.wide_exact.WideExact.mul,h1,h2,h3,h4,h5,h6,h7,h8,h9,bind_tc_ok]

theorem wide_scale (x : NE) (s : U32) :
    map wide (FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x s) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (wide x) s := by
  obtain ⟨rhs,a,b,hr,cr,ha,ca,hb,cb,hz⟩ := NEB_WideCalls.scale x s
  have aa := transport qm _ _ a (qm_scale x.c0 rhs) ha
  have bb := transport qm _ _ b (qm_scale x.c1 rhs) hb
  rw [hz]
  simp only [map,wide,AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31,
    AspisR1CurrentWide.field.P,hr,aa,bb,bind_tc_ok]

#print axioms transport
#print axioms m_add
#print axioms m_sub
#print axioms m_mul
#print axioms reduce
#print axioms m_reduce
#print axioms m_double
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_scale
#print axioms cm_mul
#print axioms by_r
#print axioms qm_add
#print axioms qm_sub
#print axioms qm_scale
#print axioms qm_mul
#print axioms mul_u
#print axioms wide_add
#print axioms wide_sub
#print axioms wide_mul
#print axioms wide_scale
end NEI_ReleaseField
end
