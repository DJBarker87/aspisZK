import S9HighTermsTraceV1
import S9HighPowerPrefixSemanticsV1
import S9ArrayWriteScheduleRootV1
import S9SourceSideUpdatesRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S9HighTermPolynomialMeaningRootV1
open AspisR1S9HelperP6
open S2LibraFactoredIdentity
local instance concreteOps : FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
abbrev W := field.WideExact
abbrev Q := field.QM31
abbrev D := AspisR1S9HighTermsTraceV1.decW
abbrev DQ := AspisR1S9HighTermsTraceV1.decQ
abbrev cell {α : Type} (a : Array α (4#usize)) (j : Fin 4) :=
  S9ArrayWriteScheduleRootV1.cells a j

theorem source_read_cell {α : Type} (a : Array α (4#usize))
    (i : Usize) (x : α) (hi : i.val < 4)
    (h : Array.index_usize a i = .ok x) : cell a ⟨i.val,hi⟩ = x := by
  obtain ⟨r,hr,hv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec a i (by simpa [a.property] using hi))
  have heq : r = x := Result.ok.inj (hr.symm.trans h)
  exact hv.symm.trans heq

theorem source_perm_cells (j : Fin 4) :
    (cell weights.PERM j).val = (perm j).val := by
  fin_cases j <;> norm_num [cell, S9ArrayWriteScheduleRootV1.cells,
    weights.PERM, Array.make, perm]

theorem actual_term_source_cell
    (ap1 : Array W (4#usize)) (high : Array Q (4#usize))
    (i : Usize) (hi : i.val < 4)
    (call : AspisR1S9HighTermsConcreteV1.HighTermCall ap1 high i) :
    cell ap1 (perm ⟨i.val,hi⟩) = call.x := by
  have hread := source_read_cell weights.PERM i call.perm hi call.perm_read
  have hp : call.perm.val = (perm ⟨i.val,hi⟩).val := by
    rw [← hread]
    exact source_perm_cells ⟨i.val,hi⟩
  have hpBound : call.perm.val < 4 := by rw [hp]; exact (perm ⟨i.val,hi⟩).isLt
  have hx := source_read_cell ap1 call.perm call.x hpBound call.ap1_read
  have hfin : (⟨call.perm.val,hpBound⟩ : Fin 4) = perm ⟨i.val,hi⟩ := Fin.ext hp
  rw [hfin] at hx
  exact hx

#print axioms source_read_cell
#print axioms source_perm_cells
#print axioms actual_term_source_cell
end AspisR1.S9HighTermPolynomialMeaningRootV1
