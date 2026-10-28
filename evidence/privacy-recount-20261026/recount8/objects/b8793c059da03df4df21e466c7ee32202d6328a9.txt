import PV_B3P_EncodeSuccess226
namespace PV_B3P_EncodeLength226
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false
attribute [local irreducible] reference226.chunk reference226.chunk8 reference226.byte_at
set_option backward.isDefEq.respectTransparency false in
theorem success_length (p : reference226.OwnedPublic)
    (chunks : Array (Array U8 64#usize) 23#usize) (n : Usize)
    (h : reference226.encode_owned p = .ok (.Ok (chunks,n))) :
    n = if p.withdrawal then 1427#usize else 1455#usize := by
  rw [PV_B3P_EncodeLaw226.complete_result] at h
  unfold PV_B3P_EncodeLaw226.spec at h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v0,hv0,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v1,hv1,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v2,hv2,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v3,hv3,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v4,hv4,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v5,hv5,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v6,hv6,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v7,hv7,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v8,hv8,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v9,hv9,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v10,hv10,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v11,hv11,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v12,hv12,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v13,hv13,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v14,hv14,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v15,hv15,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v16,hv16,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v17,hv17,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v18,hv18,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v19,hv19,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v20,hv20,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v21,hv21,h⟩ := h
  rw [PV_B3P_ResultSuccess226.bind_success] at h
  obtain ⟨v22,hv22,h⟩ := h
  have he := core.result.Result.Ok.inj (Result.ok.inj h)
  exact (congrArg Prod.snd he).symm
#print axioms success_length
end PV_B3P_EncodeLength226
