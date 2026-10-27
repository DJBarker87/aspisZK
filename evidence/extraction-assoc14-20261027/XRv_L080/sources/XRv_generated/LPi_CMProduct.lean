import LPi_NatBase
set_option autoImplicit false
namespace AspisR1.LPi_CMProduct
open Aeneas Aeneas.Std Result LPi_Total
abbrev NC := FIo_Native.aspis_core.field.CM31

def Canon (x : NC) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647

def realWord (a b c d : Nat) := ((a*c)%2147483647+2147483647-(b*d)%2147483647)%2147483647
def imagWord (a b c d : Nat) :=
  ((((a+b)*(c+d))%2147483647+2147483647-(a*c)%2147483647)%2147483647+
    2147483647-(b*d)%2147483647)%2147483647

def sum (x : NC) : U64 := U64.wrapping_add
  (core.convert.num.FromU64U32.from x.a) (core.convert.num.FromU64U32.from x.b)
def cross (x y : NC) : U64 := U64.wrapping_mul (sum x) (sum y)

theorem sum_value (x : NC) : (sum x).val=x.a.val+x.b.val := by
  unfold sum
  rw [U64.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
  rfl

theorem cross_value (x y : NC) (hx : Canon x) (hy : Canon y) :
    (cross x y).val=(x.a.val+x.b.val)*(y.a.val+y.b.val) := by
  unfold cross
  rw [U64.wrapping_mul_val_eq,sum_value,sum_value]
  apply Nat.mod_eq_of_lt
  have h0 : x.a.val+x.b.val < 4294967296 := by obtain ⟨_,_⟩ := hx; omega
  have h1 : y.a.val+y.b.val < 4294967296 := by obtain ⟨_,_⟩ := hy; omega
  have h := Nat.mul_lt_mul_of_lt_of_lt h0 h1
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits] at h ⊢
  exact h

theorem source (x y : NC) (hx : Canon x) (hy : Canon y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y = ok z ∧ Canon z ∧
      z.a.val = realWord x.a.val x.b.val y.a.val y.b.val ∧
      z.b.val = imagWord x.a.val x.b.val y.a.val y.b.val := by
  obtain ⟨m0,h0,v0,c0⟩ := LPf_BaseMultiply.source x.a y.a
  obtain ⟨m1,h1,v1,c1⟩ := LPf_BaseMultiply.source x.b y.b
  obtain ⟨m2,h2,v2,c2⟩ := LPf_CoreReduction.source (cross x y)
  have hr : FIo_Native.aspis_core.field.M31.reduce_u64 (cross x y) = ok m2 := by
    simp only [FIo_Native.aspis_core.field.M31.reduce_u64,h2,bind_tc_ok]
  obtain ⟨a,ha,va,ca⟩ := LPi_NatBase.sub m0 m1 c0 c1
  obtain ⟨b,hb,vb,cb⟩ := LPi_NatBase.sub m2 m0 c2 c0
  obtain ⟨c,hc,vc,cc⟩ := LPi_NatBase.sub b m1 cb c1
  refine ⟨⟨a,c⟩,?_,⟨ca,cc⟩,?_,?_⟩
  · simp only [FIo_Native.aspis_core.field.CM31.mul,h0,h1,lift,bind_tc_ok]
    change (do let t ← FIo_Native.aspis_core.field.M31.reduce_u64 (cross x y)
               let a ← FIo_Native.aspis_core.field.M31.sub m0 m1
               let b ← FIo_Native.aspis_core.field.M31.sub t m0
               let c ← FIo_Native.aspis_core.field.M31.sub b m1
               ok (⟨a,c⟩ : NC)) = _
    simp only [hr,ha,hb,hc,bind_tc_ok]
  · simpa only [realWord,v0,v1] using va
  · rw [cross_value x y hx hy] at v2
    simpa only [imagWord,vb,v2,v0,v1] using vc

#print axioms sum_value
#print axioms cross_value
#print axioms source
end AspisR1.LPi_CMProduct
