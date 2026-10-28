import PV_B3P_InstalledBuffer226
namespace PV_B3P_SelectedValue226
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false in
theorem success_value (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install226V3.Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_B3P_Install226V3.Types base)) (out : alloc.vec.Vec U8)
    (h : @ExternalFuns.op226 (PV_B3P_Install226V3.Types base)
      (PV_B3P_Install226V3.selected base ops) p = .ok (.Ok out)) :
    out.val = PV_B3P_ByteLayout226V3.layout
      (PV_B3P_ProjectV3Law226.value (PV_B3P_PublicCarrier226V3.toSource base p)) := by
  rw [PV_B3P_Install226V3.source] at h
  generalize hr : PV_B3P_226V3.reference226.public_bytes
    (PV_B3P_PublicCarrier226V3.toSource base p) = r at h
  cases r with
  | fail e => cases h
  | div => cases h
  | ok inner =>
    cases inner with
    | Err e => cases h
    | Ok packet =>
      rcases packet with ⟨chunks,n⟩
      have he : PV_B3P_ByteOutput226.bytes chunks n = out :=
        core.result.Result.Ok.inj (Result.ok.inj h)
      rw [← he]
      exact PV_B3P_InstalledBuffer226.reference_value _ chunks n hr
#print axioms success_value
end
end PV_B3P_SelectedValue226
