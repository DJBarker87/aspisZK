import CuSavingsDelayedScalar
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.CuSavingsDelayedArrays
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1DelayedDots AspisV8R17.RawReducer
open CuSavingsResidues CuSavingsDelayedScalar
abbrev Raw := Array U64 8#usize
abbrev Canon := Array U32 8#usize
abbrev Range := core.ops.range.Range Usize

def wordAt {T : Type} (a : Array T 8#usize) (j : Fin 8) : T :=
  a.val[j.val]'(by simpa [a.property] using j.isLt)

theorem read {T : Type} (a : Array T 8#usize) (i : Usize) (hi : i.val < 8) :
    Array.index_usize a i = .ok (wordAt a ⟨i.val,hi⟩) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with | none => Result.fail Error.arrayOutOfBounds | some x => Result.ok x) = _
  rw [List.getElem?_eq_getElem hidx]
  rfl

theorem update {T : Type} (a : Array T 8#usize) (i : Usize) (hi : i.val < 8) (v : T) :
    Array.update a i v = .ok (a.set i v) := by
  obtain ⟨out,hr,heq⟩ := WP.spec_imp_exists (Array.update_spec a i v
    (by simpa [a.property] using hi))
  simpa only [heq] using hr

theorem at_set {T : Type} (a : Array T 8#usize) (i : Usize) (v : T) (j : Fin 8) :
    wordAt (a.set i v) j = if j.val = i.val then v else wordAt a j := by
  simp only [wordAt,Array.set_val_eq,List.getElem_set]
  split <;> split <;> simp_all

def State (count upto : Nat) (old : Canon) (raw : Raw) : Prop :=
  ∀ j : Fin 8, (wordAt old j).val = (wordAt raw j).val%P ∧
    (wordAt raw j).val < (count + if j.val < upto then 2 else 1)*FoldBound

theorem scalar_step (old : U32) (raw sum : U64) (count : Nat)
    (hc : count < 7) (he : old.val = raw.val%P)
    (hr : raw.val < (count+1)*FoldBound) :
    ∃ (o : U32) (r : U64),
      (do let s ← field.M31.reduce_u64 sum; field.M31.add old s) = .ok o ∧
      foldAdd raw sum = .ok r ∧ o.val = r.val%P ∧ r.val < (count+2)*FoldBound := by
  obtain ⟨s,hs,hsv,hsc⟩ := reducer_mod sum
  obtain ⟨o,ho,hov,hoc⟩ := add_mod old s
    (by rw [he];exact Nat.mod_lt _ (by decide)) hsc
  obtain ⟨r,hrun,hrv,hrb,hrm⟩ := foldAdd_success raw sum count hc hr
  refine ⟨o,r,by rw [hs,bind_tc_ok,ho],hrun,?_,hrb⟩
  rw [hov,he,hsv,←Nat.add_mod,hrm]

theorem state_step (count upto : Nat) (old : Canon) (raw : Raw) (i : Usize)
    (hi : i.val < 8) (hu : i.val = upto) (h : State count upto old raw)
    (o : U32) (r : U64) (he : o.val = r.val%P)
    (hr : r.val < (count+2)*FoldBound) :
    State count (upto+1) (old.set i o) (raw.set i r) := by
  intro j
  simp only [at_set]
  by_cases hj : j.val = i.val
  · simp only [hj,↓reduceIte,hu,Nat.lt_succ_self]
    exact ⟨he,hr⟩
  · simp only [hj,↓reduceIte]
    have hne : j.val ≠ upto := by omega
    by_cases hl : j.val < upto
    · have hn : j.val < upto+1 := by omega
      simpa only [hl,hn,↓reduceIte] using h j
    · have hn : ¬ j.val < upto+1 := by omega
      simpa only [hl,hn,↓reduceIte] using h j

#print axioms scalar_step
#print axioms state_step
end AspisR1.CuSavingsDelayedArrays
