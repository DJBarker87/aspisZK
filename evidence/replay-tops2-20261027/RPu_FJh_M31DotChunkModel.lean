import RPu_FJh_M31DotChunkSource
import RPu_FJh_M31DotReads

/-! Symbolic bounded chunk execution. Each actual input adds its four
coordinate products; the source loop is not evaluated at a concrete size. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotChunkModel
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (cell)
open AspisR1.FJh_InternalClosureSums (Raw4)
open AspisR1.FJh_M31DotInput (Budget)
open AspisR1.FJh_M31DotChunkSource (Range source_loop_eq)
open AspisR1.FJh_M31DotReads

theorem loop_success_fuel (weights : Slice field.QM31) (values : Slice U32)
    (raw : Raw4) (iter : Range) (fuel n : Nat)
    (hwEnd : iter.end.val ≤ weights.val.length) (hvEnd : iter.end.val ≤ values.val.length)
    (hspan : iter.start.val+fuel=iter.end.val) (hcount : n+fuel ≤ 4)
    (hw : CanonicalWeights weights) (hv : CanonicalValues values) (hb : Budget raw n) :
    ∃ out : Raw4, field.qm31_m31_dot_loop1_loop0 iter weights values raw = .ok out ∧
      Budget out (n+fuel) ∧ ∀ j : Fin 4,
        (cell out j).val = (cell raw j).val + remaining weights values iter.start.val fuel j := by
  induction fuel generalizing raw iter n with
  | zero =>
    have hstop : iter.start.val ≥ iter.end.val := by omega
    have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
    refine ⟨raw,?_,?_,?_⟩
    · rw [source_loop_eq,hnext]
      rfl
    · simpa only [Nat.add_zero] using hb
    · intro j
      simp only [remaining,Nat.add_zero]
  | succ fuel ih =>
    have hactive : iter.start.val < iter.end.val := by omega
    have hwidx : iter.start.val < weights.val.length := by omega
    have hvidx : iter.start.val < values.val.length := by omega
    let q := sliceCell weights iter.start.val hwidx
    let v := sliceCell values iter.start.val hvidx
    have hreadQ : Slice.index_usize weights iter.start = .ok q := source_read weights iter.start hwidx
    have hreadV : Slice.index_usize values iter.start = .ok v := source_read values iter.start hvidx
    obtain ⟨nextRaw,hinput,hnextBudget,hinputModel⟩ :=
      AspisR1.FJh_M31DotInput.source_success raw q v n (by omega) hb
        (hw iter.start.val hwidx) (hv iter.start.val hvidx)
    obtain ⟨iter1,hnext,hinc,hend1,_⟩ := AspisR1.OccupancyRangeTraversal.next_step iter hactive
    have hwEnd1 : iter1.end.val ≤ weights.val.length := by rw [hend1]; exact hwEnd
    have hvEnd1 : iter1.end.val ≤ values.val.length := by rw [hend1]; exact hvEnd
    have hspan1 : iter1.start.val+fuel=iter1.end.val := by rw [hend1]; omega
    have hcount1 : (n+1)+fuel ≤ 4 := by omega
    obtain ⟨out,hrun,houtBudget,houtModel⟩ :=
      ih nextRaw iter1 (n+1) hwEnd1 hvEnd1 hspan1 hcount1 hnextBudget
    refine ⟨out,?_,?_,?_⟩
    · rw [source_loop_eq,hnext]
      change (do
        let value ← Slice.index_usize values iter.start
        let weight ← Slice.index_usize weights iter.start
        let nextRaw1 ← AspisR1.FJh_M31DotInput.run raw weight value
        field.qm31_m31_dot_loop1_loop0 iter1 weights values nextRaw1) = .ok out
      simp only [hreadV,hreadQ,hinput,bind_tc_ok]
      exact hrun
    · have heq : (n+1)+fuel = n+(fuel+1) := by omega
      simpa only [heq] using houtBudget
    · intro j
      have h := houtModel j
      rw [hinc,hinputModel j] at h
      have ht : term weights values iter.start.val j =
          (cell (AspisR1.FJh_InternalStateWords.wordVec q) j).val * v.val :=
        term_read weights values iter.start hwidx hvidx j
      change (cell out j).val = (cell raw j).val +
        (term weights values iter.start.val j + remaining weights values (iter.start.val+1) fuel j)
      rw [ht,← Nat.add_assoc]
      exact h

theorem source_success (weights : Slice field.QM31) (values : Slice U32) (iter : Range) (fuel : Nat)
    (hwEnd : iter.end.val ≤ weights.val.length) (hvEnd : iter.end.val ≤ values.val.length)
    (hspan : iter.start.val+fuel=iter.end.val) (hsize : fuel ≤ 4)
    (hw : CanonicalWeights weights) (hv : CanonicalValues values) :
    ∃ out : Raw4, field.qm31_m31_dot_loop1_loop0 iter weights values
        AspisR1.FJh_InternalAccumulateState.zero = .ok out ∧
      Budget out fuel ∧ ∀ j : Fin 4,
        (cell out j).val = remaining weights values iter.start.val fuel j := by
  have hz : Budget AspisR1.FJh_InternalAccumulateState.zero 0 := by
    intro j
    rw [AspisR1.FJh_InternalAccumulateState.zero_value]
    exact Nat.zero_le _
  obtain ⟨out,hrun,hb,hm⟩ := loop_success_fuel weights values
    AspisR1.FJh_InternalAccumulateState.zero iter fuel 0 hwEnd hvEnd hspan
    (by simpa only [Nat.zero_add] using hsize) hw hv hz
  refine ⟨out,hrun,?_,?_⟩
  · simpa only [Nat.zero_add] using hb
  · intro j
    have h := hm j
    rw [AspisR1.FJh_InternalAccumulateState.zero_value,Nat.zero_add] at h
    exact h

#print axioms loop_success_fuel
#print axioms source_success
end AspisR1.FJh_M31DotChunkModel
