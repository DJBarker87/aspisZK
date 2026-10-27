import RPu_FJh_M31DotSource
import RPu_FJh_InternalClosureSums

/-! One actual chunk-reduction update. The existing unrestricted U64
reducer supplies a canonical M31 residue; only bounded addition is new. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotReduceStep
open Aeneas Aeneas.Std Result WP
open FIq_Native
open AspisR1.FJh_Base (cell cell_set)
open AspisR1.FJh_InternalClosureSums (Raw4 RawBound)
open AspisR1.ExtractedMaskReducerOps
open AspisV8R17.RawReducer (P)

def step (sums raw : Raw4) (limb : Usize) : Result Raw4 := do
  let input ← Array.index_usize raw limb
  let residue ← field.M31.reduce_u64 input
  let word ← lift (UScalar.cast .U64 residue)
  let old ← Array.index_usize sums limb
  let value ← UScalar.add old word
  Array.update sums limb value

theorem source_success (sums raw : Raw4) (limb : Usize) (hi : limb.val < 4)
    (n : Nat) (hn : n ≤ 19) (hs : RawBound sums (n*P)) :
    ∃ value : U64, step sums raw limb = .ok (sums.set limb value) ∧
      RawBound (sums.set limb value) ((n+1)*P) ∧
      ∀ j : Fin 4, (cell (sums.set limb value) j).val =
        if j.val = limb.val then
          (cell sums (⟨limb.val,hi⟩ : Fin 4)).val + (cell raw (⟨limb.val,hi⟩ : Fin 4)).val % P
        else (cell sums j).val := by
  let index : Fin 4 := ⟨limb.val,hi⟩
  let input := cell raw index
  let old := cell sums index
  have hb : limb.val < (4#usize).val := by simpa using hi
  have hreadRaw : Array.index_usize raw limb = .ok input := by
    simpa only [input,index,cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok raw limb hb
  have hreadOld : Array.index_usize sums limb = .ok old := by
    simpa only [old,index,cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok sums limb hb
  obtain ⟨residue,hreduce,hmod,hcanonical⟩ := AspisR1.ExtractedMaskReducer.current_wrapper_mod input
  have hreduce : FIq_Native.field.M31.reduce_u64 input = .ok residue :=
    (FIv_NativeArithmetic.m31_reduce input).trans hreduce
  have hcast : (UScalar.cast .U64 residue).val = residue.val :=
    AspisR1.ExtractedMaskReducer.cast_widen_value residue
  have hold : old.val < n*P := hs index
  have hlimit : 20*P < 2^64 := by norm_num [P]
  have hnBound : n*P ≤ 19*P := Nat.mul_le_mul_right P hn
  have hsum : old.val + residue.val < (n+1)*P := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have hsum64 : old.val + (UScalar.cast .U64 residue).val < 2^64 := by rw [hcast]; omega
  obtain ⟨value,hadd,hvalue⟩ := add_success old (UScalar.cast .U64 residue) hsum64
  rw [hcast] at hvalue
  have hwrite : Array.update sums limb value = .ok (sums.set limb value) := by
    obtain ⟨out,hrun,hset⟩ := WP.spec_imp_exists (Array.update_spec sums limb value
      (by simpa [sums.property] using hb))
    simpa only [hset] using hrun
  refine ⟨value,?_,?_,?_⟩
  · simp only [step,hreadRaw,hreadOld,hreduce,hadd,hwrite,lift,bind_tc_ok]
  · intro j
    rw [cell_set]
    by_cases hj : j.val = limb.val
    · simp only [if_pos hj]
      rw [hvalue]
      exact hsum
    · simp only [if_neg hj]
      rw [Nat.add_mul,Nat.one_mul]
      exact Nat.lt_of_lt_of_le (hs j) (Nat.le_add_right (n*P) P)
  · intro j
    rw [cell_set]
    by_cases hj : j.val = limb.val
    · simp only [if_pos hj]
      rw [hvalue,hmod]
    · simp only [if_neg hj]

#print axioms source_success
end AspisR1.FJh_M31DotReduceStep
