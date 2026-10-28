import PV_B3P_FieldResult226V3
import PV_B3P_Repeat226
namespace PV_B3P_FrontierOutcome226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_ByteScalar226V3
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error

def frontierAt (a : Array (Array U32 8#usize) 20#usize) (i : Usize) :
    Result (core.result.Result U8 E) := do
  let q ← i / 32#usize
  let r ← i % 32#usize
  let s ← r / 4#usize
  let row ← Array.index_usize a q
  let m ← Array.index_usize row s
  let t ← i % 4#usize
  reference226.field_byte m t

theorem no_outer_failure (a : Array (Array U32 8#usize) 20#usize) (i : Usize)
    (hi : i.val < 640) :
    ∃ v, frontierAt a i = .ok v := by
  obtain ⟨q,hq,hqval⟩ := UScalar.div_spec (x:=i) (y:=32#usize) (by decide)
  obtain ⟨r,hr,hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=i) (y:=32#usize) (by decide))
  obtain ⟨s,hs,hsval⟩ := UScalar.div_spec (x:=r) (y:=4#usize) (by decide)
  obtain ⟨t,ht,htval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=i) (y:=4#usize) (by decide))
  have hqnat : q.val = i.val / 32 := by simpa using hqval
  have hrnat : r.val = i.val % 32 := by simpa using hrval
  have hsnat : s.val = r.val / 4 := by simpa using hsval
  have hqb : q.val < (20#usize).val := by
    have hn : (20#usize).val = 20 := rfl
    rw [hn,hqnat]; omega
  have hsb : s.val < (8#usize).val := by
    have hn : (8#usize).val = 8 := rfl
    rw [hn,hsnat,hrnat]; omega
  have hql : q.val < a.val.length := by simpa [a.property] using hqb
  let row := a.val[q.val]'hql
  have hsl : s.val < row.val.length := by simpa [row.property] using hsb
  refine ⟨PV_B3P_FieldResult226V3.value (row.val[s.val]'hsl) t, ?_⟩
  unfold frontierAt
  rw [hq]
  simp only [bind_tc_ok]
  rw [hr]
  simp only [bind_tc_ok]
  rw [hs]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a q hqb]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value row s hsb]
  simp only [bind_tc_ok]
  rw [ht]
  simp only [bind_tc_ok]
  exact PV_B3P_FieldResult226V3.complete_result _ _

#print axioms no_outer_failure
end PV_B3P_FrontierOutcome226V3
