import ExtractorCubicBitEnvelopeM10

/-! A conservative per-step allocation reservation. A step may copy a whole
bounded protocol object or one log-sized list; every reserved slot also pays
quadratic index/operand bit work. This intentionally gives a quartic envelope.
It does not infer an allocation trace from returned-value equality. The caller
must use a complete work schedule and a protocol footprint/natural envelope. -/
set_option autoImplicit false
namespace AspisR1.ExtractorReservedResourcesM10
open RawExtractorCostComposedV2

def resources (W R L A N : Nat) : Resources :=
  let slots := W*(A+L+1)
  ⟨W,R,slots*(L+N+1)^2+slots*256⟩

def constant (C A N : Nat) : Nat := C+A+N+256+12976224+1

theorem total_bound (W R L C A N : Nat)
    (hw : W ≤ C*(L+1)) (hr : R ≤ 12976224*L) :
    (resources W R L A N).total ≤ 4*(constant C A N)^4*(L+1)^4 := by
  let D := constant C A N
  let U := D*(L+1)
  have hc : C ≤ D := by unfold D constant; omega
  have ha : A+1 ≤ D := by unfold D constant; omega
  have hn : N+1 ≤ D := by unfold D constant; omega
  have hd : 12976224 ≤ D := by unfold D constant; omega
  have hwidth : 256 ≤ D := by unfold D constant; omega
  have hD : 1 ≤ D := by omega
  have hdu : D ≤ U := Nat.le_mul_of_pos_right D (by omega)
  have hU : 1 ≤ U := hD.trans hdu
  have hWU : W ≤ U := hw.trans (Nat.mul_le_mul_right _ hc)
  have hRU : R ≤ U := hr.trans (by unfold U; nlinarith)
  have hAU : A+L+1 ≤ U := by unfold U; nlinarith
  have hNU : L+N+1 ≤ U := by unfold U; nlinarith
  have hslots := Nat.mul_le_mul hWU hAU
  have hbits := Nat.mul_le_mul hslots (Nat.pow_le_pow_left hNU 2)
  have halloc := Nat.mul_le_mul hslots (hwidth.trans hdu)
  have htw : U*U = U^2 := by ring
  have hfour : (U*U)*U^2 = U^4 := by ring
  have hthree : (U*U)*U = U^3 := by ring
  rw [hfour] at hbits
  rw [hthree] at halloc
  have hu3 : U^3 ≤ U^4 := Nat.pow_le_pow_right hU (by omega)
  have hu4 : U ≤ U^4 := by simpa only [pow_one] using (Nat.pow_le_pow_right hU (show 1 ≤ 4 by omega))
  have hh : W+R+(W*(A+L+1)*(L+N+1)^2+W*(A+L+1)*256) ≤ 4*U^4 := by omega
  simpa only [resources,Resources.total,U,D,Nat.mul_pow,Nat.mul_assoc] using hh

#print axioms total_bound
end AspisR1.ExtractorReservedResourcesM10
