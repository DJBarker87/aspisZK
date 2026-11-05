import NHT_PacketOps
import NFW_PowersCohort
set_option autoImplicit false
noncomputable section
namespace NHT_PowersDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- The SAME powers call supplies NFS's coefficient domain; no unrelated array
or assumed successful output enters the driver interface. -/
theorem produced (gamma : aspis_core.field.wide_exact.WideExact)
 (canonical : NFN_LPi_FieldValues.canonE (FIo_Install.toE gamma)) :
 ∃ g : Array NFN_LPi_FieldValues.NE 29#usize,
 FIo_Native.weights.powers 29#usize (FIo_Install.toE gamma)=ok g ∧
 NHT_PacketOps.powers 29#usize gamma=ok (FIp_DotsAdapter.fromArray g) ∧
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (FIp_DotsAdapter.fromArray g)) := by
 obtain ⟨g,native,_⟩ := NFW_LPi_PowersSource.source 29#usize (FIo_Install.toE gamma) canonical
 exact ⟨g,native,NHT_PacketOps.powers_reply _ _ _ native,
  NFW_PowersDomain.query_domain _ canonical g native⟩
#print axioms produced
end NHT_PowersDomain
