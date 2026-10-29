import LPi_TowerValues
set_option autoImplicit false
namespace NEA_ScaleProduct
open Aeneas Aeneas.Std Result AspisR1.LPi_FieldValues

def scaleC (x : CW) (s : Nat) : CW := ((x.1*s)%2147483647,(x.2*s)%2147483647)
def scaleQ (x : QW) (s : Nat) : QW := (scaleC x.1 s,scaleC x.2 s)
def scaleE (x : EW) (s : Nat) : EW := (scaleQ x.1 s,scaleQ x.2 s)

theorem cm (x : NC) (s : U32) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul_m31 x s=ok z ∧ canonC z ∧
      cw z=scaleC (cw x) s.val := by
  obtain ⟨a,ha,va,ca⟩ := AspisR1.LPf_BaseMultiply.source x.a s
  obtain ⟨b,hb,vb,cb⟩ := AspisR1.LPf_BaseMultiply.source x.b s
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.CM31.mul_m31,ha,hb,bind_tc_ok]

theorem qm (x : NQ) (s : U32) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul_m31 x s=ok z ∧ canonQ z ∧
      qw z=scaleQ (qw x) s.val := by
  obtain ⟨a,ha,ca,va⟩ := cm x.c0 s
  obtain ⟨b,hb,cb,vb⟩ := cm x.c1 s
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.QM31.mul_m31,ha,hb,bind_tc_ok]

theorem wide (x : NE) (s : U32) (canonical : s.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x s=ok z ∧ canonE z ∧
      ew z=scaleE (ew x) s.val := by
  obtain ⟨r,rem,value⟩ := WP.spec_imp_exists
    (UScalar.rem_spec s (y:=FIo_Native.aspis_core.field.P)
      (by norm_num [FIo_Native.aspis_core.field.P]))
  have same : r=s := by
    apply UScalar.eq_of_val_eq
    rw [value]
    apply Nat.mod_eq_of_lt
    simpa [FIo_Native.aspis_core.field.P] using canonical
  rw [same] at rem
  obtain ⟨a,ha,ca,va⟩ := qm x.c0 s
  obtain ⟨b,hb,cb,vb⟩ := qm x.c1 s
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31,rem,ha,hb,bind_tc_ok]

#print axioms cm
#print axioms qm
#print axioms wide
#print axioms AspisR1.LPi_TowerValues.wide_mul
end NEA_ScaleProduct
