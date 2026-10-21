import S8OwnedP6ValueModel
import S8OwnedP6LoopContracts

/-! Arbitrary-length refinement of the complete emitted owned finish loop. -/
set_option autoImplicit false
noncomputable section
namespace S8OwnedP6Finish
open Aeneas Aeneas.Std Result ControlFlow
open S8OwnedP6 S8OwnedP6ValueModel
abbrev Raw := alloc.vec.Vec Row
abbrev Weights := alloc.vec.Vec Q

def modelValue (row : Row) : Q := (value_total_model row).choose

theorem modelValue_success (row : Row) : value_owned row=.ok (modelValue row) :=
  (value_total_model row).choose_spec.1

theorem modelValue_coordinates (row : Row) (j : Fin 4) :
    (coordinate (modelValue row) j).val=(rowAt row j).val%2147483647 ∧
      (coordinate (modelValue row) j).val<2147483647 :=
  (value_total_model row).choose_spec.2 j

def Inv (raw : Raw) (old : Weights) (state : Weights × Usize) : Prop :=
  state.1.length=old.length ∧ state.2.val≤old.length ∧
    ∀ j, state.1.val[j]? =
      if j<state.2.val then (raw.val[j]?).map modelValue else old.val[j]?

/-- The emitted Vec loop succeeds under the exact raw/destination length
precondition and returns the canonical reduction of every destination row.
No term count, raw-limb bound or callee-success premise is needed. -/
theorem finish_total_model (raw : Raw) (old : Weights)
    (hlen : old.length≤raw.length) :
    ∃ out : Weights, finish_owned raw old=.ok out ∧ out.length=old.length ∧
      ∀ j, j<old.length → out.val[j]?=(raw.val[j]?).map modelValue := by
  have spec : WP.spec (finish_owned raw old) (fun out => out.length=old.length ∧
      ∀ j, j<old.length → out.val[j]?=(raw.val[j]?).map modelValue) := by
    unfold finish_owned finish_owned_loop
    refine loop.spec_decr_nat (fun s : Weights × Usize => old.length-s.2.val)
      (Inv raw old)
      (fun out => out.length=old.length ∧ ∀ j, j<old.length →
        out.val[j]?=(raw.val[j]?).map modelValue)
      (fun s => finish_owned_loop.body raw s.1 s.2) (old,0#usize) ?_ ?_
    · rintro ⟨weights,index⟩ ⟨hsize,hindex,hcells⟩
      change weights.length=old.length at hsize
      change index.val≤old.length at hindex
      by_cases hi : index.val<weights.length
      · have hr : index.val<raw.length := by omega
        obtain ⟨row,hread,hrow⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec raw index hr)
        have hread' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row) raw index=.ok row := by
          rw [alloc.vec.Vec.index_slice_index]; exact hread
        obtain ⟨⟨previous,back⟩,hmut,_hprev,hback⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.index_mut_usize_spec weights index hi)
        have hmut' : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Q) weights index=.ok (previous,back) := by
          rw [alloc.vec.Vec.index_mut_slice_index]; exact hmut
        have hcap : index.val+1≤Usize.max := by
          have hp : old.length≤Usize.max := old.property
          omega
        have sadd : WP.spec (index+1#usize : Result Usize) (fun n => n.val=index.val+1) := by
          apply UScalar.add_spec
          change index.val+1 ≤ Usize.max
          exact hcap
        obtain ⟨next,hnext,hval⟩ := WP.spec_imp_exists sadd
        change next.val=index.val+1 at hval
        have hcond : index<alloc.vec.Vec.len weights := hi
        have body : finish_owned_loop.body raw weights index=
            .ok (.cont (back (modelValue row),next)) := by
          simp only [finish_owned_loop.body,if_pos hcond,hread',hmut',modelValue_success,bind_tc_ok,hnext]
        rw [body,WP.spec_ok]
        have hback' : back (modelValue row)=alloc.vec.Vec.set weights index (modelValue row) := congrFun hback _
        rw [hback']
        constructor
        · refine ⟨?_,by omega,?_⟩
          · simpa [alloc.vec.Vec.length,alloc.vec.Vec.set] using hsize
          · intro j
            change (weights.val.set index.val (modelValue row))[j]? = _
            by_cases hj : index.val=j
            · subst j
              rw [List.getElem?_set_self hi,if_pos (by omega)]
              rw [List.getElem?_eq_getElem hr,hrow]
              rfl
            · rw [List.getElem?_set_ne hj,hcells j]
              have he : (j<next.val) ↔ j < index.val := by omega
              simp only [he]
        · change old.length-next.val < old.length-index.val
          omega
      · have hcond : ¬ index<alloc.vec.Vec.len weights := hi
        simp only [finish_owned_loop.body,if_neg hcond,WP.spec_ok]
        refine ⟨hsize,?_⟩
        intro j hj
        have he : index.val=old.length := by omega
        simpa only [he,if_pos hj] using hcells j
    · refine ⟨rfl,by simp,?_⟩
      intro j
      change old.val[j]? = if j<0 then _ else _
      simp only [Nat.not_lt_zero,if_false]
  obtain ⟨out,hrun,hpost⟩ := WP.spec_imp_exists spec
  exact ⟨out,hrun,hpost⟩

#print axioms modelValue_success
#print axioms modelValue_coordinates
#print axioms finish_total_model
end S8OwnedP6Finish
