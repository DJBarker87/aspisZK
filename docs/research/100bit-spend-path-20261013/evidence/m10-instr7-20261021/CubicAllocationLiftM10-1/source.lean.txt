import ExtractorFixedWidthResourcesM10

/-! Fixed-width primitive bit pricing plus a separately supplied cumulative
allocation-bit counter. No allocation fact is inferred from work or value.
The only unmirrored component is explicitly exposed by AllocationBound below.
Polynomial/field dimensions are protocol constants; L is only the log size. -/
set_option autoImplicit false
namespace AspisR1.CubicAllocationLiftM10
open RawExtractorCostComposedV2

def resources (W R heap L N : Nat) : Resources :=
  ⟨W,R,W*(L+N+257)^2+heap⟩

def constant (C A N : Nat) : Nat := C+A+N+12976224+257+1

theorem total_bound (W R heap L C A N : Nat)
    (hw : W ≤ C*(L+1)) (hr : R ≤ 12976224*L) (ha : heap ≤ A*(L+1)) :
    (resources W R heap L N).total ≤ 4*(constant C A N)^3*(L+1)^3 := by
  let D := constant C A N
  let U := D*(L+1)
  have hc : C ≤ D := by unfold D constant; omega
  have ha' : A ≤ D := by unfold D constant; omega
  have hn : N+257 ≤ D := by unfold D constant; omega
  have hd : 12976224 ≤ D := by unfold D constant; omega
  have hD : 1 ≤ D := by unfold D constant; omega
  have hdu : D ≤ U := Nat.le_mul_of_pos_right D (by omega)
  have hU : 1 ≤ U := hD.trans hdu
  have hWU : W ≤ U := hw.trans (Nat.mul_le_mul_right _ hc)
  have hRU : R ≤ U := hr.trans (by unfold U; nlinarith)
  have hAU : heap ≤ U := ha.trans (Nat.mul_le_mul_right _ ha')
  have hNU : L+N+257 ≤ U := by unfold U; nlinarith
  have hbits := Nat.mul_le_mul hWU (Nat.pow_le_pow_left hNU 2)
  have heq : U*U^2 = U^3 := by ring
  rw [heq] at hbits
  have hcube : U ≤ U^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hU (show 1 ≤ 3 by omega)
  have hh : W+R+(W*(L+N+257)^2+heap) ≤ 4*U^3 := by omega
  simpa only [resources,Resources.total,U,D,Nat.mul_pow,Nat.mul_assoc] using hh

#print axioms total_bound
end AspisR1.CubicAllocationLiftM10
