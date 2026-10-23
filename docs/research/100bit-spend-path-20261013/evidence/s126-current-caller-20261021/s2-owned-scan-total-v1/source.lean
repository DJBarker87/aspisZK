import S2OwnedStage1ModelV1

set_option autoImplicit false
namespace S2OwnedCheckpointScanTotalV1
open Aeneas Aeneas.Std Result ControlFlow
open AspisS2OwnedStage1

def ZeroAt (bytes : alloc.vec.Vec U8) (j : Nat) : Prop :=
  bytes.val[j]? = some 0#u8

private theorem add_total (a : Usize) (h : a.val + 1 ≤ Usize.max) :
    ∃ b : Usize, (a + 1#usize : Result Usize) = ok b ∧ b.val = a.val + 1 := by
  apply WP.spec_imp_exists
  apply UScalar.add_spec
  simpa only [UScalar.max_USize_eq] using h

theorem scan_step (bytes : alloc.vec.Vec U8) (index : Usize)
    (hi : index.val < bytes.val.length) :
    ∃ next : Usize, next.val = index.val + 1 ∧
      owned_checkpoint_nonzero_loop.body bytes index =
        ok (if ZeroAt bytes index.val then cont next else done (some true)) := by
  obtain ⟨byte,hread,hbyte⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec bytes index hi)
  have hread' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8)
      bytes index = ok byte := by
    rw [alloc.vec.Vec.index_slice_index]
    exact hread
  have hlength : bytes.val.length ≤ Usize.max := bytes.property
  obtain ⟨next,hnext,hnv⟩ := add_total index (by omega)
  have hcond : index < alloc.vec.Vec.len bytes := hi
  have hz : ZeroAt bytes index.val ↔ byte = 0#u8 := by
    unfold ZeroAt
    rw [List.getElem?_eq_getElem hi, ← hbyte]
    exact Option.some.injEq
  refine ⟨next,hnv,?_⟩
  by_cases hb : byte = 0#u8
  · have hzero := hz.mpr hb
    simp [owned_checkpoint_nonzero_loop.body, hcond, hread', hb, hnext, hzero]
  · have hnonzero : ¬ZeroAt bytes index.val := fun h => hb (hz.mp h)
    simp [owned_checkpoint_nonzero_loop.body, hcond, hread', hb, hnonzero]

/-- The actual emitted owned scan is TOTAL for every representable Vec length
and all U8 contents. No successful traversal/index/addition is assumed. -/
theorem scan_total (bytes : alloc.vec.Vec U8) :
    ∃ out : Bool, owned_checkpoint_nonzero bytes = ok out ∧
      (out = false ↔ ∀ j, j < bytes.val.length → ZeroAt bytes j) := by
  let allZero := ∀ j, j < bytes.val.length → ZeroAt bytes j
  have hs : WP.spec (owned_checkpoint_nonzero_loop bytes 0#usize)
      (fun out => (out = none ↔ allZero) ∧ (out = none ∨ out = some true)) := by
    unfold owned_checkpoint_nonzero_loop
    refine loop.spec_decr_nat (fun i : Usize => bytes.val.length - i.val)
      (fun i => i.val ≤ bytes.val.length ∧ ∀ j, j < i.val → ZeroAt bytes j)
      (fun out => (out = none ↔ allZero) ∧ (out = none ∨ out = some true))
      (fun i => owned_checkpoint_nonzero_loop.body bytes i) 0#usize ?_ ?_
    · intro i hinv
      rcases hinv with ⟨hib,hprefix⟩
      by_cases hi : i.val < bytes.val.length
      · obtain ⟨next,hnv,hstep⟩ := scan_step bytes i hi
        by_cases hz : ZeroAt bytes i.val
        · rw [hstep, if_pos hz, WP.spec_ok]
          constructor
          · refine ⟨by omega,?_⟩
            intro j hj
            by_cases he : j = i.val
            · subst j; exact hz
            · exact hprefix j (by omega)
          · omega
        · rw [hstep, if_neg hz, WP.spec_ok]
          refine ⟨?_, Or.inr rfl⟩
          constructor
          · intro h; cases h
          · intro ha; exact False.elim (hz (ha i.val hi))
      · have hc : ¬i < alloc.vec.Vec.len bytes := hi
        simp only [owned_checkpoint_nonzero_loop.body, if_neg hc, WP.spec_ok]
        refine ⟨?_, Or.inl rfl⟩
        constructor
        · intro _ j hj; exact hprefix j (by omega)
        · intro _; rfl
    · exact ⟨by change (0:Nat) ≤ bytes.val.length; omega,
        by intro j hj; change j < (0:Nat) at hj; omega⟩
  obtain ⟨out,hrun,hequiv,hcases⟩ := WP.spec_imp_exists hs
  cases hcases with
  | inl h =>
    subst out
    refine ⟨false,?_,?_⟩
    · simp only [owned_checkpoint_nonzero, hrun, bind_tc_ok]
    · exact ⟨fun _ => hequiv.mp rfl, fun _ => rfl⟩
  | inr h =>
    subst out
    refine ⟨true,?_,?_⟩
    · simp only [owned_checkpoint_nonzero, hrun, bind_tc_ok]
    · constructor
      · intro h; cases h
      · intro h; have hn := hequiv.mpr h; cases hn

#print axioms scan_step
#print axioms scan_total
end S2OwnedCheckpointScanTotalV1
