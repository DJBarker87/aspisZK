import PV_B3Q_RangeActual
namespace PV_B3Q_InclusiveActual
open Aeneas Aeneas.Std PV_B3P_Groups14227 core.ops.range
set_option autoImplicit false
def source (r : RangeInclusive Usize) : Result (Option Usize × RangeInclusive Usize) :=
 if r.exhausted = true ∨ r.«end».val < r.start.val then .ok (none,r)
 else if r.start.val < r.«end».val then
  .ok (some r.start,{r with start := Usize.wrapping_add r.start 1#usize})
 else .ok (some r.start,{r with exhausted := true})
def model := core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepUsize

theorem binding (r : RangeInclusive Usize) : source r = model r := by
 have clone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by intro x; rfl
 have lt_ : ∀ x y : Usize, core.cmp.PartialOrdUsize.lt x y = .ok (decide (x.val < y.val)) := by intro x y; rfl
 have le_ : ∀ x y : Usize, core.cmp.PartialOrdUsize.le x y = .ok (decide (x.val ≤ y.val)) := by intro x y; rfl
 obtain ⟨⟨item,next⟩,run,post⟩ := WP.spec_imp_exists
  (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_UScalar_spec clone lt_ le_ r)
 change model r = .ok (item,next) at run
 change (if r.exhausted = true ∨ r.«end».val < r.start.val then item=none ∧ next=r
  else if r.start.val < r.«end».val then
   item=some r.start ∧ next.start.val=r.start.val+1 ∧ next.«end»=r.«end» ∧ next.exhausted=false
  else item=some r.start ∧ next.start=r.start ∧ next.«end»=r.«end» ∧ next.exhausted=true) at post
 rw [run]
 by_cases empty : r.exhausted = true ∨ r.«end».val < r.start.val
 · rw [if_pos empty] at post
   rw [source,if_pos empty,post.1,post.2]
 · have inex : r.exhausted=false := by
    cases he : r.exhausted with
    | false => rfl
    | true => exact False.elim (empty (Or.inl he))
   by_cases active : r.start.val < r.«end».val
   · rw [if_neg empty,if_pos active] at post
     have wrap : (Usize.wrapping_add r.start 1#usize).val=r.start.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      exact Nat.mod_eq_of_lt
       (PV_B3P_Binding13227.range_increment_safe13 r.start r.«end» (by scalar_tac))
     have startSame := UScalar.eq_of_val_eq (post.2.1.trans wrap.symm)
     have nextSame : next={r with start := Usize.wrapping_add r.start 1#usize} := by
      cases next
      cases r
      simp_all
     rw [source,if_neg empty,if_pos active,post.1,nextSame]
   · rw [if_neg empty,if_neg active] at post
     have nextSame : next={r with exhausted := true} := by
      cases next
      cases r
      simp_all
     rw [source,if_neg empty,if_neg active,post.1,nextSame]

theorem actual_inclusive_link : PV_B3P_Link_std_dependency_closure14
 (fun _ : Unit => RangeInclusive Usize → Result (Option Usize × RangeInclusive Usize))
 (fun _ => source) (fun _ => model) := by
 intro _
 funext r
 exact binding r
#print axioms binding
#print axioms actual_inclusive_link
end PV_B3Q_InclusiveActual
