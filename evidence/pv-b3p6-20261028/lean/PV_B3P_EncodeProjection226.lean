import PV_B3P_BytesV3Emission226
import PV_B3P_ChunkV3Law226
import PV_B3P_ResultSuccess226
namespace PV_B3P_EncodeProjection226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
attribute [local irreducible] reference226.byte_at reference226.chunk8 reference226.chunk
def start (q : Nat) (hq : q < 23) : Usize := Usize.ofNatCore (64*q) (by
  have hb := Usize.cMax_bound_concrete.1
  scalar_tac)
theorem start_val (q : Nat) (hq : q < 23) : (start q hq).val = 64*q := rfl
#print axioms start_val
set_option backward.isDefEq.respectTransparency false in
theorem success_chunk (p : reference226.OwnedPublic)
    (chunks : Array (Array U8 64#usize) 23#usize) (n : Usize)
    (h : reference226.encode_owned p = .ok (.Ok (chunks,n)))
    (q : Nat) (hq : q < 23) :
    reference226.chunk p (start q hq) =
      .ok (.Ok (chunks.val[q]'(by rw [chunks.property]; simpa using hq))) := by
  unfold reference226.encode_owned at h
  cases hw : p.withdrawal
  all_goals
    have hu : {p with withdrawal := p.withdrawal} = p := by cases p; rfl
    try simp only [hw] at hu
    simp only [hw,Bool.false_eq_true,↓reduceIte,lift,bind_tc_ok,hu,try_bind_eq] at h
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
    have he : (Array.make 23#usize [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22] (by rfl), (if p.withdrawal then 1427#usize else 1455#usize)) = (chunks,n) := by
      simpa only [hw,Bool.false_eq_true,↓reduceIte] using core.result.Result.Ok.inj (Result.ok.inj h)
    cases he
    have hc : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 ∨ q = 22 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hs : start 0 (by decide) = 0#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv0
    · have hs : start 1 (by decide) = 64#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv1
    · have hs : start 2 (by decide) = 128#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv2
    · have hs : start 3 (by decide) = 192#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv3
    · have hs : start 4 (by decide) = 256#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv4
    · have hs : start 5 (by decide) = 320#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv5
    · have hs : start 6 (by decide) = 384#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv6
    · have hs : start 7 (by decide) = 448#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv7
    · have hs : start 8 (by decide) = 512#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv8
    · have hs : start 9 (by decide) = 576#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv9
    · have hs : start 10 (by decide) = 640#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv10
    · have hs : start 11 (by decide) = 704#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv11
    · have hs : start 12 (by decide) = 768#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv12
    · have hs : start 13 (by decide) = 832#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv13
    · have hs : start 14 (by decide) = 896#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv14
    · have hs : start 15 (by decide) = 960#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv15
    · have hs : start 16 (by decide) = 1024#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv16
    · have hs : start 17 (by decide) = 1088#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv17
    · have hs : start 18 (by decide) = 1152#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv18
    · have hs : start 19 (by decide) = 1216#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv19
    · have hs : start 20 (by decide) = 1280#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv20
    · have hs : start 21 (by decide) = 1344#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv21
    · have hs : start 22 (by decide) = 1408#usize := by
        apply UScalar.eq_of_val_eq
        rfl
      simpa only [hs,Array.make,List.getElem_cons_zero,List.getElem_cons_succ] using hv22
#print axioms success_chunk
end PV_B3P_EncodeProjection226
