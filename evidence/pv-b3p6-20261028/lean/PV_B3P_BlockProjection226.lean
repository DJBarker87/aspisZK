import PV_B3P_Chunk64Law226
import PV_B3P_ResultSuccess226
import PV_B3P_Chunk8Projection226
import PV_B3P_LayoutCells226V3
import PV_B3P_Offset226V3
namespace PV_B3P_BlockProjection226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult
set_option autoImplicit false
attribute [local irreducible] reference226.byte_at reference226.chunk8 reference226.chunk
def offset (q : Nat) (hq : q < 8) : Usize := Usize.ofNatCore (8*q) (by
  have hb := Usize.cMax_bound_concrete.1
  scalar_tac)
theorem offset_val (q : Nat) (hq : q < 8) : (offset q hq).val = 8*q := rfl
#print axioms offset_val
set_option backward.isDefEq.respectTransparency false in
theorem success_blocks (p : reference226.OwnedPublic) (base : Usize)
    (out : Array U8 64#usize) (h : reference226.chunk p base = .ok (.Ok out)) :
    ∃ (bs : List (Array U8 8#usize)) (hlen : bs.length = 8),
      out = PV_B3P_Chunk64Law226.join bs hlen ∧
      ∀ (q : Nat) (hq : q < 8), reference226.chunk8 p (Usize.wrapping_add base (offset q hq)) =
        .ok (.Ok (bs[q]'(by omega))) := by
  rw [PV_B3P_Chunk64Law226.complete_result] at h
  unfold PV_B3P_Chunk64Law226.spec at h
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
  refine ⟨[v0,v1,v2,v3,v4,v5,v6,v7],rfl,?_,?_⟩
  · exact (core.result.Result.Ok.inj (Result.ok.inj h)).symm
  · intro q hq
    have hc : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hs : offset 0 (by decide) = 0#usize := by apply UScalar.eq_of_val_eq; rfl
      simpa only [hs,List.getElem_cons_zero,List.getElem_cons_succ] using hv0
    · have hs : offset 1 (by decide) = 8#usize := by apply UScalar.eq_of_val_eq; rfl
      simpa only [hs,List.getElem_cons_zero,List.getElem_cons_succ] using hv1
    · have hs : offset 2 (by decide) = 16#usize := by apply UScalar.eq_of_val_eq; rfl
      simpa only [hs,List.getElem_cons_zero,List.getElem_cons_succ] using hv2
    · have hs : offset 3 (by decide) = 24#usize := by apply UScalar.eq_of_val_eq; rfl
      simpa only [hs,List.getElem_cons_zero,List.getElem_cons_succ] using hv3
    · have hs : offset 4 (by decide) = 32#usize := by apply UScalar.eq_of_val_eq; rfl
      simpa only [hs,List.getElem_cons_zero,List.getElem_cons_succ] using hv4
    · have hs : offset 5 (by decide) = 40#usize := by apply UScalar.eq_of_val_eq; rfl
      simpa only [hs,List.getElem_cons_zero,List.getElem_cons_succ] using hv5
    · have hs : offset 6 (by decide) = 48#usize := by apply UScalar.eq_of_val_eq; rfl
      simpa only [hs,List.getElem_cons_zero,List.getElem_cons_succ] using hv6
    · have hs : offset 7 (by decide) = 56#usize := by apply UScalar.eq_of_val_eq; rfl
      simpa only [hs,List.getElem_cons_zero,List.getElem_cons_succ] using hv7
#print axioms success_blocks
set_option backward.isDefEq.respectTransparency false in
theorem success_cell (p : reference226.OwnedPublic) (base : Usize)
    (out : Array U8 64#usize) (h : reference226.chunk p base = .ok (.Ok out))
    (hb : base.val + 64 < UScalar.size .Usize) (r : Usize) (hr : r.val < 64) :
    reference226.byte_at p (Usize.wrapping_add base r) =
      .ok (.Ok (out.val[r.val]'(by rw [out.property]; simpa using hr))) := by
  obtain ⟨bs,hlen,hout,hbs⟩ := success_blocks p base out h
  have hq : r.val / 8 < 8 := by omega
  let j : Usize := Usize.ofNatCore (r.val % 8) (by
    have hx := Usize.cMax_bound_concrete.1
    scalar_tac)
  have hj : j.val = r.val % 8 := rfl
  have hj8 : j.val < 8 := by rw [hj]; omega
  have hv := PV_B3P_Chunk8Projection226.success_cell p
    (Usize.wrapping_add base (offset (r.val/8) hq)) _ (hbs _ hq) j hj8
  have hoff : (Usize.wrapping_add base (offset (r.val/8) hq)).val = base.val + 8*(r.val/8) := by
    rw [PV_B3P_Offset226V3.add_value _ _ (by rw [offset_val]; omega),offset_val]
  have hadd : Usize.wrapping_add (Usize.wrapping_add base (offset (r.val/8) hq)) j =
      Usize.wrapping_add base r := by
    apply UScalar.eq_of_val_eq
    rw [PV_B3P_Offset226V3.add_value _ _ (by rw [hoff,hj]; omega),hoff,hj,
      PV_B3P_Offset226V3.add_value _ _ (by omega)]
    omega
  rw [hadd] at hv
  have hflat := PV_B3P_LayoutCells226V3.flat_cell 8
    (fun a : Array U8 8#usize => a.val) (fun a => a.property)
    bs (r.val/8) (r.val%8) (by omega) (by omega)
  have hid : 8*(r.val/8)+r.val%8 = r.val := by omega
  rw [hid] at hflat
  have houtval : out.val = bs.flatMap (fun a => a.val) := congrArg Subtype.val hout
  rw [← houtval] at hflat
  rw [List.getElem?_eq_getElem (by rw [out.property]; simpa using hr),
      List.getElem?_eq_getElem (by rw [(bs[r.val/8]'(by omega)).property]; change r.val % 8 < 8; omega)] at hflat
  have heq := Option.some.inj hflat
  simpa only [hj,heq] using hv
#print axioms success_cell
end PV_B3P_BlockProjection226
