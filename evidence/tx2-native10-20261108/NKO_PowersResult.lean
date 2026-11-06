import NKO_C02Source
set_option autoImplicit false
noncomputable section
namespace NKO_PowersResult
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
/-- Invert only the actual returned powers bind. No totality or independent
array is postulated; fail and div cannot reach the query occurrence. -/
theorem returned (gamma : aspis_core.field.wide_exact.WideExact)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (call : NHT_PacketOps.powers 29#usize gamma=ok g) :
 ∃ native : Array FIo_Install.NE 29#usize,
 FIo_Native.weights.powers 29#usize (FIo_Install.toE gamma)=ok native ∧
 FIp_DotsAdapter.fromArray native=g := by
 unfold NHT_PacketOps.powers at call
 cases step : FIo_Native.weights.powers 29#usize (FIo_Install.toE gamma) with
 | fail e => rw [step] at call;cases call
 | div => rw [step] at call;cases call
 | ok native =>
  rw [step] at call
  exact ⟨native,rfl,Result.ok.inj call⟩
#print axioms returned
end NKO_PowersResult
