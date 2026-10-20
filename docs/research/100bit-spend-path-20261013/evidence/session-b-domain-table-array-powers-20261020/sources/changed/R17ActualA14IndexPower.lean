import R17NarrowFunsA14ChunkPower
import R17ActualTableArrayIndexV1
import R17ActualTableEntriesIndices
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace R17ActualA14IndexPower
open AspisR1QueryGeometryActual R17TableBasePowerBridge R17TableExponentDomainBridge

theorem getElem_eq_of_getElem?_eq {α : Type} (xs : List α) (i : Nat)
    (hidx : i < xs.length) {x : α} (h : xs[i]? = some x) :
    xs[i]'hidx = x := by
  rw [List.getElem?_eq_getElem hidx] at h
  exact Option.some.inj h

theorem actual_table_a14_index_power (j : Nat) (hj : j < 32)
    (i : Usize) (hidx : i.val = 448 + j) :
    ∀ p, Array.index_usize AspisR1QueryGeometryActual.fast_domain.TABLE_A i = .ok p →
      R17TableBasePowerBridge.decode
        (R17TableAChunk14Certificate.toNatC (⟨p.1.val, p.2.val⟩ : R17TableBasePowerProbe.C)) =
        R17TableBasePowerBridge.zPow
          (R17TableBasePowerBridge.decode
            (R17TableAChunk14Certificate.toNatC R17TableBasePowerProbe.gen))
          (R17TableExponentDomainBridge.leftExponent (448 + j)) := by
  have hbound : i.val < 512 := by rw [hidx]; omega
  have harray := R17ActualTableArrayIndexV1.tableA_index_entries i hbound
  have hopt := R17ActualTableEntriesIndices.a14_entry_index j hj
  rw [← hidx] at hopt
  have hoptSome : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[i.val]? =
      some (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[j]'(by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14_length]; exact hj)) := by
    calc
      AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[i.val]? = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[j]? := hopt
      _ = some (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[j]'(by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14_length]; exact hj)) :=
        List.getElem?_eq_getElem (by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14_length]; exact hj)
  have hEntries : i.val < AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries.length := by
    rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries_length]
    exact hbound
  have hdata : AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries[i.val]'(by
      rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries_length]; exact hbound) =
      AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[j]'(by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14_length]; exact hj) :=
    getElem_eq_of_getElem?_eq AspisR1QueryGeometryActual.fast_domain.TABLE_A_entries i.val hEntries hoptSome
  have harray' : Array.index_usize AspisR1QueryGeometryActual.fast_domain.TABLE_A i =
      .ok (AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[j]'(by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14_length]; exact hj)) :=
    harray.trans (congrArg Result.ok hdata)
  intro p hp
  have hp' : p = AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14[j]'(by rw [AspisR1QueryGeometryActual.fast_domain.TABLE_A_chunk_14_length]; exact hj) := by
    rw [harray'] at hp
    cases hp
    rfl
  cases hp'
  interval_cases j
  all_goals
    first
    | exact R17NarrowFunsA14ChunkPower.cell_00_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_01_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_02_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_03_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_04_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_05_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_06_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_07_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_08_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_09_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_10_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_11_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_12_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_13_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_14_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_15_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_16_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_17_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_18_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_19_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_20_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_21_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_22_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_23_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_24_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_25_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_26_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_27_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_28_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_29_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_30_circle_power
    | exact R17NarrowFunsA14ChunkPower.cell_31_circle_power

#print axioms actual_table_a14_index_power
end R17ActualA14IndexPower
