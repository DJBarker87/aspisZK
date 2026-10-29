import LPi_TowerValues
set_option autoImplicit false
namespace NEA_WideLinear
open Aeneas Aeneas.Std Result AspisR1.LPi_FieldValues AspisR1.LPi_TowerValues

def addE (x y : EW) : EW := (addQ x.1 y.1,addQ x.2 y.2)
def subE (x y : EW) : EW := (subQ x.1 y.1,subQ x.2 y.2)
theorem add (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z ∧ canonE z ∧
      ew z=addE (ew x) (ew y) := by
  obtain ⟨a,ha,ca,va⟩ := qm_add x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := qm_add x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,ha,hb,bind_tc_ok]
theorem sub (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.sub x y=ok z ∧ canonE z ∧
      ew z=subE (ew x) (ew y) := by
  obtain ⟨a,ha,ca,va⟩ := qm_sub x.c0 y.c0 hx.1 hy.1
  obtain ⟨b,hb,cb,vb⟩ := qm_sub x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a,b⟩,?_,⟨ca,cb⟩,Prod.ext va vb⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.sub,ha,hb,bind_tc_ok]

theorem add_branch (x y : Nat) (hx : x<2147483647) (hy : y<2147483647) :
    addM x y = if x+y≥2147483647 then x+y-2147483647 else x+y := by
  unfold addM
  split
  · rw [← Nat.mod_add_div (x+y) 2147483647]
    omega
  · apply Nat.mod_eq_of_lt
    omega

theorem sub_branch (x y : Nat) (hx : x<2147483647) (hy : y<2147483647) :
    subM x y = if x≥y then x-y else 2147483647-y+x := by
  unfold subM
  split
  · have e : x+2147483647-y=(x-y)+2147483647 := by omega
    rw [e,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  · apply Nat.mod_eq_of_lt
    omega
#print axioms add
#print axioms sub
#print axioms add_branch
#print axioms sub_branch
end NEA_WideLinear
