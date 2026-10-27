import RPv_FJh_InternalClosureSums

/-! One exact source update in the four-limb raw accumulator. All arithmetic
bounds are symbolic; no recurrence or field operation is evaluated. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalAccumulateStep
open Aeneas Aeneas.Std Result WP
open FIq_Native
open AspisR1.FJh_Base (cell cell_set)
open AspisR1.FJh_InternalClosureSums (Raw4 Words4 RawBound CanonicalWords)
open AspisR1.FJh_InternalWordOps (wide wide_value)
open AspisR1.ExtractedMaskReducerOps AspisV8R17.RawReducer

def step (part : Raw4) (words : Words4) (limb : Usize) : Result Raw4 := do
  let word ← Array.index_usize words limb
  let old ← Array.index_usize part limb
  let added ← UScalar.add old (wide word)
  Array.update part limb added

theorem step_success (part : Raw4) (words : Words4) (limb : Usize) (n : Nat)
    (hi : limb.val < 4) (hn : n ≤ 19) (hp : RawBound part (n*P)) (hw : CanonicalWords words) :
    ∃ value : U64, step part words limb = .ok (part.set limb value) ∧
      RawBound (part.set limb value) ((n+1)*P) ∧
      ∀ j : Fin 4, (cell (part.set limb value) j).val =
        if j.val = limb.val then
          (cell part (⟨limb.val,hi⟩ : Fin 4)).val + (cell words (⟨limb.val,hi⟩ : Fin 4)).val
        else (cell part j).val := by
  let index : Fin 4 := ⟨limb.val,hi⟩
  let p := cell part index
  let w := cell words index
  have hb : limb.val < (4#usize).val := by simpa using hi
  have hreadP : Array.index_usize part limb = .ok p := by
    simpa only [p,cell,index] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok part limb hb
  have hreadW : Array.index_usize words limb = .ok w := by
    simpa only [w,cell,index] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok words limb hb
  have hpLocal : p.val < n*P := hp index
  have hwLocal : w.val < P := hw index
  have hnMul : n*P ≤ 19*P := Nat.mul_le_mul_right P hn
  have hsucc : (n+1)*P = n*P+P := by rw [Nat.add_mul,Nat.one_mul]
  have hbound : p.val+w.val < (n+1)*P := by rw [hsucc]; omega
  have hlimit : 20*P < 2^64 := by norm_num [P]
  have hb64 : p.val+(wide w).val < 2^64 := by rw [wide_value]; omega
  obtain ⟨value,hadd,hvalue⟩ := add_success p (wide w) hb64
  rw [wide_value] at hvalue
  obtain ⟨out,hupdate,hset⟩ := WP.spec_imp_exists
    (Array.update_spec part limb value (by simpa [part.property] using hb))
  have hwrite : Array.update part limb value = .ok (part.set limb value) := by rw [hupdate,hset]
  refine ⟨value,?_,?_,?_⟩
  · simp only [step,hreadW,hreadP,hadd,hwrite,bind_tc_ok]
  · intro j
    rw [cell_set]
    by_cases hj : j.val = limb.val
    · simp only [if_pos hj]
      rw [hvalue]
      exact hbound
    · simp only [if_neg hj]
      rw [hsucc]
      exact Nat.lt_of_lt_of_le (hp j) (Nat.le_add_right (n*P) P)
  · intro j
    rw [cell_set]
    by_cases hj : j.val = limb.val
    · simp only [if_pos hj]
      exact hvalue
    · simp only [if_neg hj]

theorem source_step (part : Raw4) (words : Words4) (limb : Usize) :
    state_only_poseidon.internal_linear_lazy_loop0_loop0 part words limb =
      (if limb < 4#usize then do
        let nextPart ← step part words limb
        let nextLimb ← UScalar.add limb 1#usize
        state_only_poseidon.internal_linear_lazy_loop0_loop0 nextPart words nextLimb
      else .ok part) := by
  rw [state_only_poseidon.internal_linear_lazy_loop0_loop0.eq_def]
  simp only [step,bind_assoc_eq,lift,bind_tc_ok]
  rfl

#print axioms step_success
#print axioms source_step
end AspisR1.FJh_InternalAccumulateStep
