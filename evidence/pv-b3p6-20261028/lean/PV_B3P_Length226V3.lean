import PV_B3P_EncodeTag226V3
import PV_B3P_ProjectV3Law226
import PV_B3P_Install226V3
namespace PV_B3P_Length226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

theorem source_tag (p : reference226.Source) (chunks : PV_B3P_ByteOutput226.Chunks)
    (n : Usize) (h : reference226.public_bytes p = .ok (.Ok (chunks,n))) :
    n = if (PV_B3P_ProjectV3Law226.value p).withdrawal then 1427#usize else 1455#usize := by
  rw [PV_B3P_ProjectV3Law226.complete_source] at h
  exact PV_B3P_EncodeTag226V3.tag _ _ _ h

theorem output_length (p : reference226.Source) (chunks : PV_B3P_ByteOutput226.Chunks)
    (n : Usize) (h : reference226.public_bytes p = .ok (.Ok (chunks,n))) :
    (PV_B3P_ByteOutput226.bytes chunks n).val.length =
      if (PV_B3P_ProjectV3Law226.value p).withdrawal then 1427 else 1455 := by
  rw [PV_B3P_ByteOutput226.bytes_length,source_tag p chunks n h]
  have h1427 : (1427#usize).val = 1427 := rfl
  have h1455 : (1455#usize).val = 1455 := rfl
  cases hw : (PV_B3P_ProjectV3Law226.value p).withdrawal <;>
    simp only [hw,Bool.false_eq_true,↓reduceIte,h1427,h1455] <;> omega

theorem installed_length (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_B3P_Install226V3.Types base))
    (p : @ProverRwFull.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_B3P_Install226V3.Types base)) (out : alloc.vec.Vec U8)
    (h : @ProverRwFull.ExternalFuns.op226 (PV_B3P_Install226V3.Types base)
      (PV_B3P_Install226V3.selected base ops) p = .ok (.Ok out)) :
    out.val.length = if (PV_B3P_ProjectV3Law226.value
      (PV_B3P_PublicCarrier226V3.toSource base p)).withdrawal then 1427 else 1455 := by
  rw [PV_B3P_Install226V3.source] at h
  generalize hr : reference226.public_bytes (PV_B3P_PublicCarrier226V3.toSource base p) = r at h
  cases r with
  | fail e => cases h
  | div => cases h
  | ok inner =>
    cases inner with
    | Err e => cases h
    | Ok pair =>
      obtain ⟨chunks,n⟩ := pair
      have he : out = PV_B3P_ByteOutput226.bytes chunks n := by cases h; rfl
      rw [he]
      exact output_length _ _ _ hr

#print axioms source_tag
#print axioms output_length
#print axioms installed_length
end PV_B3P_Length226V3
