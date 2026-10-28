import PV_B3P_ByteScalar226V3
import PV_B3P_Repeat226
namespace PV_B3P_DigestTotal226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteScalar226V3
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error

def digestAt (a : Array U32 8#usize) (i : Usize) :
    Result (core.result.Result U8 E) := do
  let q ← i / 4#usize
  let m ← Array.index_usize a q
  let r ← i % 4#usize
  reference226.field_byte m r

theorem success (a : Array U32 8#usize) (i : Usize) (hi : i.val < 32)
    (hc : ∀ m ∈ a.val, m < 2147483647#u32) :
    ∃ v, digestAt a i = .ok (.Ok v) := by
  obtain ⟨q,hq,hqval⟩ := UScalar.div_spec (x:=i) (y:=4#usize) (by decide)
  obtain ⟨r,hr,hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=i) (y:=4#usize) (by decide))
  have hqnat : q.val = i.val / 4 := by simpa using hqval
  have hqbound : q.val < (8#usize).val := by
    have h8 : (8#usize).val = 8 := by rfl
    rw [h8,hqnat]
    omega
  have hlen : q.val < a.val.length := by simpa [a.property] using hqbound
  have hcanonical := hc (a.val[q.val]'hlen) (List.getElem_mem hlen)
  refine ⟨_,?_⟩
  unfold digestAt
  rw [hq]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a q hqbound]
  simp only [bind_tc_ok]
  rw [hr]
  simp only [bind_tc_ok]
  exact field_success _ _ hcanonical

#print axioms success
end PV_B3P_DigestTotal226V3
