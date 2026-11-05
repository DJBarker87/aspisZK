import NGW_CurrentAddPort
import RPt_FIo_M31MulBridge
import RPt_FIo_M31SubBridge
set_option autoImplicit false
namespace NHE_CMPort
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem sub (x y : NC) (hx : canonC x) (hy : canonC y) :
 (do let z ← FIo_Native.aspis_core.field.CM31.sub x y;ok (FIo_FieldBridge.cm z))=
 AspisR1CurrentWide.field.CM31.sub (FIo_FieldBridge.cm x) (FIo_FieldBridge.cm y) := by
 simp only [FIo_Native.aspis_core.field.CM31.sub,AspisR1CurrentWide.field.CM31.sub,FIo_FieldBridge.cm,bind_assoc_eq,bind_tc_ok]
 rw [FIo_M31SubBridge.sub x.a y.a hx.1 hy.1,FIo_M31SubBridge.sub x.b y.b hx.2 hy.2]

theorem mul (x y : NC) (hx : canonC x) (hy : canonC y) :
 (do let z ← FIo_Native.aspis_core.field.CM31.mul x y;ok (FIo_FieldBridge.cm z))=
 AspisR1CurrentWide.field.CM31.mul (FIo_FieldBridge.cm x) (FIo_FieldBridge.cm y) := by
 obtain ⟨m0,h0,_,c0⟩ := LPf_BaseMultiply.source x.a y.a
 obtain ⟨m1,h1,_,c1⟩ := LPf_BaseMultiply.source x.b y.b
 obtain ⟨m2,h2,_,c2⟩ := LPf_CoreReduction.source (LPi_CMProduct.cross x y)
 have hsum (z : NC) :
  (core.convert.num.FromU64U32.from z.a)+(core.convert.num.FromU64U32.from z.b)=ok (LPi_CMProduct.sum z) :=
  FIo_ScalarBridge.add _ _ (by scalar_tac)
 have hprod : (LPi_CMProduct.sum x)*(LPi_CMProduct.sum y)=ok (LPi_CMProduct.cross x y) := by
  apply FIo_ScalarBridge.mul
  rw [LPi_CMProduct.sum_value,LPi_CMProduct.sum_value]
  have bx : x.a.val+x.b.val<4294967296 := by rcases hx with ⟨_,_⟩;omega
  have by' : y.a.val+y.b.val<4294967296 := by rcases hy with ⟨_,_⟩;omega
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt bx by') (by decide)
 obtain ⟨a,ha,_,ca⟩ := LPi_NatBase.sub m0 m1 c0 c1
 obtain ⟨b,hb,_,cb⟩ := LPi_NatBase.sub m2 m0 c2 c0
 obtain ⟨c,hc,_,_⟩ := LPi_NatBase.sub b m1 cb c1
 have h0' := (FIo_M31MulBridge.same x.a y.a).symm.trans h0
 have h1' := (FIo_M31MulBridge.same x.b y.b).symm.trans h1
 have h2' := (FIo_ReduceBridge.same (LPi_CMProduct.cross x y)).symm.trans h2
 have ha' := (FIo_M31SubBridge.sub m0 m1 c0 c1).symm.trans ha
 have hb' := (FIo_M31SubBridge.sub m2 m0 c2 c0).symm.trans hb
 have hc' := (FIo_M31SubBridge.sub b m1 cb c1).symm.trans hc
 simp only [FIo_Native.aspis_core.field.CM31.mul,AspisR1CurrentWide.field.CM31.mul,FIo_FieldBridge.cm,h0,h1,h0',h1',lift,bind_tc_ok,hsum,hprod,←LPi_CMProduct.sum,←LPi_CMProduct.cross,FIo_Native.aspis_core.field.M31.reduce_u64,AspisR1CurrentWide.field.M31.reduce_u64,h2,h2',ha,hb,hc,ha',hb',hc',bind_tc_ok]

#print axioms sub
#print axioms mul
end NHE_CMPort
