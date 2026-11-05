import NHM_FactoredSums
import NHM_ArrayCanon
set_option autoImplicit false
namespace NHX_FieldResults
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem wide_mul (x y z : NE) (hx : canonE x) (hy : canonE y)
 (run : FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z) : canonE z := by
 obtain ⟨out,ho,co,_⟩:=LPi_TowerValues.wide_mul x y hx hy
 rw [run] at ho
 cases Result.ok.inj ho
 exact co

theorem qm_mul (x y z : NQ) (hx : canonQ x) (hy : canonQ y)
 (run : FIo_Native.aspis_core.field.QM31.mul x y=ok z) : canonQ z := by
 obtain ⟨out,ho,co,_⟩:=LPi_TowerValues.qm_mul x y hx hy
 rw [run] at ho
 cases Result.ok.inj ho
 exact co

theorem mixed (x : NE) (q : NQ) (z : NE) (hx : canonE x) (hq : canonQ q)
 (run : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x q=ok z) : canonE z := by
 obtain ⟨out,ho,co,_⟩:=NHE_ScalarProductLaw.product x q hx hq
 rw [run] at ho
 cases Result.ok.inj ho
 exact co

theorem add (x y z : NE) (hx : canonE x) (hy : canonE y)
 (run : FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z) : canonE z := by
 obtain ⟨out,ho,co⟩:=NGW_PolynomialAdd.total x y hx hy
 rw [run] at ho
 cases Result.ok.inj ho
 exact co

theorem quarter (x z : NE)
 (run : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x FIo_Native.weights.QUARTER=ok z) : canonE z := by
 obtain ⟨out,ho,co,_⟩:=NGM_RoundScale.total x
 simp only [FIo_Native.weights.QUARTER] at run
 rw [run] at ho
 cases Result.ok.inj ho
 exact co

#print axioms wide_mul
#print axioms qm_mul
#print axioms mixed
#print axioms add
#print axioms quarter
end NHX_FieldResults
