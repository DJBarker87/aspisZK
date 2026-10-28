import PV_B3P_BytesV3Emission226
import PV_B3P_ChunkV3Law226
import PV_B3P_ResultSuccess226
namespace PV_B3P_Chunk8Projection226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
attribute [local irreducible] reference226.byte_at reference226.chunk8 reference226.chunk
set_option backward.isDefEq.respectTransparency false in
theorem success_cell (p : reference226.OwnedPublic) (base : Usize)
    (out : Array U8 8#usize) (h : reference226.chunk8 p base = .ok (.Ok out))
    (j : Usize) (hj : j.val < 8) :
    reference226.byte_at p (Usize.wrapping_add base j) =
      .ok (.Ok (out.val[j.val]'(by rw [out.property]; simpa using hj))) := by
  rw [PV_B3P_ChunkV3Law226.complete_result] at h
  unfold PV_B3P_ChunkV3Law226.spec8 at h
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
  have he : Array.make 8#usize [v0,v1,v2,v3,v4,v5,v6,v7] (by rfl) = out := core.result.Result.Ok.inj (Result.ok.inj h)
  cases he
  have hc : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hje : j = 0#usize := by apply UScalar.eq_of_val_eq; exact h0
    subst j
    have hval : (0#usize).val = 0 := rfl
    simpa only [hval,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv0
  · have hje : j = 1#usize := by apply UScalar.eq_of_val_eq; exact h1
    subst j
    have hval : (1#usize).val = 1 := rfl
    simpa only [hval,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv1
  · have hje : j = 2#usize := by apply UScalar.eq_of_val_eq; exact h2
    subst j
    have hval : (2#usize).val = 2 := rfl
    simpa only [hval,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv2
  · have hje : j = 3#usize := by apply UScalar.eq_of_val_eq; exact h3
    subst j
    have hval : (3#usize).val = 3 := rfl
    simpa only [hval,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv3
  · have hje : j = 4#usize := by apply UScalar.eq_of_val_eq; exact h4
    subst j
    have hval : (4#usize).val = 4 := rfl
    simpa only [hval,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv4
  · have hje : j = 5#usize := by apply UScalar.eq_of_val_eq; exact h5
    subst j
    have hval : (5#usize).val = 5 := rfl
    simpa only [hval,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv5
  · have hje : j = 6#usize := by apply UScalar.eq_of_val_eq; exact h6
    subst j
    have hval : (6#usize).val = 6 := rfl
    simpa only [hval,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv6
  · have hje : j = 7#usize := by apply UScalar.eq_of_val_eq; exact h7
    subst j
    have hval : (7#usize).val = 7 := rfl
    simpa only [hval,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv7
#print axioms success_cell
end PV_B3P_Chunk8Projection226
