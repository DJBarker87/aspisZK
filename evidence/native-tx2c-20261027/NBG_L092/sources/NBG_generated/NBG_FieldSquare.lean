import NBG_Additive
import NBG_Reducer
set_option autoImplicit false
namespace NBG_FieldSquare
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def input (x : NC) : U64 :=
  let a := core.convert.num.FromU64U32.from x.a
  let b := core.convert.num.FromU64U32.from x.b
  let p := core.convert.num.FromU64U32.from FIo_Native.aspis_core.field.P
  U64.wrapping_mul (U64.wrapping_add a b)
    (U64.wrapping_sub (U64.wrapping_add a p) b)

theorem sub_word (x y : U64) (h : y.val ≤ x.val) :
    (U64.wrapping_sub x y).val = x.val-y.val := by
  rw [U64.wrapping_sub_val_eq]
  have hx := x.hSize
  have hy := y.hSize
  have he : x.val+(UScalar.size .U64-y.val)=(x.val-y.val)+UScalar.size .U64 := by omega
  rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]

theorem input_value (x : NC) (hx : canonC x) :
    (input x).val = (x.a.val+x.b.val)*(x.a.val+2147483647-x.b.val) := by
  let a := core.convert.num.FromU64U32.from x.a
  let b := core.convert.num.FromU64U32.from x.b
  let p := core.convert.num.FromU64U32.from FIo_Native.aspis_core.field.P
  have av : a.val=x.a.val := by scalar_tac
  have bv : b.val=x.b.val := by scalar_tac
  have pv : p.val=2147483647 := by unfold p FIo_Native.aspis_core.field.P; rfl
  have sv : (U64.wrapping_add a b).val=x.a.val+x.b.val := by
    rw [U64.wrapping_add_val_eq,av,bv,Nat.mod_eq_of_lt (by scalar_tac)]
  have ap : (U64.wrapping_add a p).val=x.a.val+2147483647 := by
    rw [U64.wrapping_add_val_eq,av,pv,Nat.mod_eq_of_lt (by scalar_tac)]
  have dv : (U64.wrapping_sub (U64.wrapping_add a p) b).val=
      x.a.val+2147483647-x.b.val := by
    rw [sub_word _ _ (by rw [ap,bv]; have := hx.2; omega),ap,bv]
  have hs : x.a.val+x.b.val<4294967296 := by rcases hx with ⟨ha,hb⟩; omega
  have hd : x.a.val+2147483647-x.b.val<4294967296 := by rcases hx with ⟨ha,hb⟩; omega
  have product : (x.a.val+x.b.val)*(x.a.val+2147483647-x.b.val)<18446744073709551616 :=
    Nat.mul_lt_mul_of_lt_of_lt hs hd
  change (U64.wrapping_mul (U64.wrapping_add a b)
    (U64.wrapping_sub (U64.wrapping_add a p) b)).val = _
  rw [U64.wrapping_mul_val_eq,sv,dv]
  apply Nat.mod_eq_of_lt
  norm_num [UScalar.size,UScalarTy.numBits]
  exact product

def squareC (x : CW) : CW :=
  (((x.1+x.2)*(x.1+2147483647-x.2))%2147483647,
    addM ((x.1*x.2)%2147483647) ((x.1*x.2)%2147483647))

theorem cm_square (x : NC) (hx : canonC x) : ∃ z,
    FIo_Native.aspis_core.field.CM31.square x = ok z ∧ canonC z ∧ cw z = squareC (cw x) := by
  obtain ⟨a,ha,va,ca⟩ := NBG_Reducer.m31_reduce (input x)
  obtain ⟨b,hb,vb,cb⟩ := LPf_BaseMultiply.source x.a x.b
  obtain ⟨c,hc,vc,cc⟩ := LPi_NatBase.add b b cb cb
  refine ⟨⟨a,c⟩,?_,⟨ca,cc⟩,Prod.ext ?_ ?_⟩
  · simp only [input] at ha
    simp only [FIo_Native.aspis_core.field.CM31.square,
      FIo_Native.aspis_core.field.M31.double,lift,bind_tc_ok,ha,hb,hc]
  · simpa only [squareC,cw,input_value x hx] using va
  · simpa only [squareC,cw,addM,vb] using vc

def squareQ (x : QW) : QW :=
  (addC (squareC x.1) (byR (squareC x.2)),
   addC (mulC x.1 x.2) (mulC x.1 x.2))

theorem qm_square (x : NQ) (hx : canonQ x) : ∃ z,
    FIo_Native.aspis_core.field.QM31.square x = ok z ∧ canonQ z ∧ qw z = squareQ (qw x) := by
  obtain ⟨a,ha,ca,va⟩ := cm_square x.c0 hx.1
  obtain ⟨b,hb,cb,vb⟩ := cm_square x.c1 hx.2
  obtain ⟨r,hr,cr,vr⟩ := LPi_FieldValues.by_r b cb
  obtain ⟨lo,hlo,clo,vlo⟩ := LPi_FieldValues.cm_add a r ca cr
  obtain ⟨cross,hcross,ccross,vcross⟩ := LPi_FieldValues.cm_mul x.c0 x.c1 hx.1 hx.2
  obtain ⟨hi,hhi,chi,vhi⟩ := NBG_Additive.cm31_double cross ccross
  refine ⟨⟨lo,hi⟩,?_,⟨clo,chi⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.QM31.square,ha,hb,hr,hlo,hcross,hhi,bind_tc_ok]
  · simp only [qw,squareQ]
    rw [vlo,vhi,vr,vcross,va,vb]

#print axioms sub_word
#print axioms input_value
#print axioms cm_square
#print axioms qm_square
end NBG_FieldSquare
