import NGU_Carriers
import RPt_FIo_WideMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGU_ClaimOps
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues
open AspisR1CurrentPreparedClaim

def claim (x : NE) : Concrete.E :=
 AspisR1ClaimPreparedBridge.toClaimE (NFW_PowersCohort.toPublic x)
def back (x : Concrete.E) : NE :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
theorem claim_back (x : Concrete.E) : claim (back x)=x := rfl

theorem multiply (x y : NE) (hx : canonE x) (hy : canonE y) :
 ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z ∧ canonE z ∧
  aspis_core.field.WideExact.mul (claim x) (claim y)=ok (claim z) := by
 obtain ⟨z,hz,cz,_⟩ := NFW_LPi_TowerValues.wide_mul x y hx hy
 obtain ⟨o,ho,co,vo⟩ := Concrete.mul_total_exact (claim x) (claim y) hx hy
 have vz := FIo_WideMulValues.mul x y z hx hy hz
 have same : back o=z := NFW_PowersInjective.injective (back o) z co cz
  (vo.trans vz.2.symm)
 have port : o=claim z := by rw [←same,claim_back]
 exact ⟨z,hz,cz,by rw [port] at ho; exact ho⟩

theorem add (x y : NE) (hx : canonE x) (hy : canonE y) :
 ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z ∧ canonE z ∧
  aspis_core.field.WideExact.add (claim x) (claim y)=ok (claim z) := by
 obtain ⟨lo,el,cl,_⟩ := NFW_LPi_TowerValues.qm_add x.c0 y.c0 hx.1 hy.1
 obtain ⟨hi,eh,ch,_⟩ := NFW_LPi_TowerValues.qm_add x.c1 y.c1 hx.2 hy.2
 let z : NE := ⟨lo,hi⟩
 have hz : FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z := by
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.add,el,eh,bind_tc_ok,z]
 have cz : canonE z := ⟨cl,ch⟩
 obtain ⟨o,ho,co,vo⟩ := Concrete.add_total_exact (claim x) (claim y) hx hy
 have vz := FIo_WideValues.add x y z hx hy hz
 have same : back o=z := NFW_PowersInjective.injective (back o) z co cz
  (vo.trans vz.2.symm)
 have port : o=claim z := by rw [←same,claim_back]
 exact ⟨z,hz,cz,by rw [port] at ho; exact ho⟩

#print axioms claim_back
#print axioms multiply
#print axioms add
end AspisR1.NGU_ClaimOps
end
