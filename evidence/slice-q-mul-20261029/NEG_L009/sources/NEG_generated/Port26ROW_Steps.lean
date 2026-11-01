import Port25ARRAY_Lane
set_option autoImplicit false
noncomputable section
namespace Port26ROW
open Aeneas Aeneas.Std Result ControlFlow
open Port23PUSH Port25ARRAY
abbrev Row := Array U64 4#usize
abbrev Power := Port23PUSH.field.QM31

def toK (q : Power) : S7Kani2AccumulatorLoop.K :=
  ⟨(q.c0.a,q.c0.b),(q.c1.a,q.c1.b)⟩

theorem row_four (row : Row) : ∃ a b c d, row = Array.make 4#usize [a,b,c,d] := by
  rcases row with ⟨l,h⟩
  change l.length = 4 at h
  rcases l with _ | ⟨a,l⟩
  · cases h
  rcases l with _ | ⟨b,l⟩
  · cases h
  rcases l with _ | ⟨c,l⟩
  · cases h
  rcases l with _ | ⟨d,l⟩
  · cases h
  rcases l with _ | ⟨e,l⟩
  · exact ⟨a,b,c,d,rfl⟩
  · simp at h

/-- One symbolic source loop unfolding, retaining checked operations and order. -/
theorem add_unroll (iter : core.ops.range.Range Usize) (row : Row)
    (basis : U32) (limbs : Array U32 4#usize) :
    verifier.update_residue_row_loop0 iter row basis limbs =
      (do let step ← verifier.update_residue_row_loop0.body limbs iter row basis
          match step with
          | done out => ok out
          | cont (it,r,b) => verifier.update_residue_row_loop0 it r b limbs) := by
  unfold verifier.update_residue_row_loop0
  rw [loop.eq_def]
  simp only [Aeneas.Std.uncurry]
  cases h : verifier.update_residue_row_loop0.body limbs iter row basis with
  | ok step => cases step with
    | done out => simp only [h,bind_tc_ok]
    | cont state => rcases state with ⟨it,r,b⟩; simp only [h,bind_tc_ok]
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]

theorem range_next (j k : Usize) (active : j.val < 4) (inc : k.val = j.val+1) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨j,4#usize⟩ =
      ok (some j,⟨k,4#usize⟩) := by
  obtain ⟨⟨o,it⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x; rfl) (by intro a b; rfl)
      ⟨j,4#usize⟩ active)
  subst o
  have hk : it.start = k := UScalar.eq_of_val_eq (by dsimp at hs; omega)
  rcases it with ⟨start,ending⟩
  dsimp at hk he
  subst start
  subst ending
  exact run

/-- Exact existing owned row on arbitrary full words. This establishes its
all-adds-then-pure-fold normal form, without claiming the mutable loop join. -/
theorem owned_four (a b c d : U64) (power : Power) (basis : U32) (flush : Bool) :
    S7Kani2OwnedRow.residue_owned (Array.make 4#usize [a,b,c,d]) (toK power) basis flush =
      (do let x0 ← addWord a power.c0.a basis
          let x1 ← addWord b power.c0.b basis
          let x2 ← addWord c power.c1.a basis
          let x3 ← addWord d power.c1.b basis
          ok (Array.make 4#usize [finish flush x0,finish flush x1,
            finish flush x2,finish flush x3])) := by
  change (do
    let x0 ← S7OwnedP6Scalar.residue_scalar_owned a power.c0.a basis flush
    let x1 ← S7OwnedP6Scalar.residue_scalar_owned b power.c0.b basis flush
    let x2 ← S7OwnedP6Scalar.residue_scalar_owned c power.c1.a basis flush
    let x3 ← S7OwnedP6Scalar.residue_scalar_owned d power.c1.b basis flush
    ok (Array.make 4#usize [x0,x1,x2,x3])) = _
  simp only [scalar_all_results,bind_assoc_eq,bind_tc_ok]

/-- ACTUAL emitted fold body, including end-of-iteration deferred back closure.
Fold totality removes its possible failure; next's Result is retained exactly. -/
theorem fold_body_complete (it : Iter U64) (back : Iter U64 → Iter U64) :
    verifier.update_residue_row_loop1.body it back =
      (do let (o,it1,nextBack) ← core.slice.iter.IteratorIterMut.next it
          match o with
          | none => ok (done (fun im => back (nextBack im none)))
          | some limb => ok (cont (it1,
              fun im => back (nextBack im (some (folded limb)))))) := by
  cases h : core.slice.iter.IteratorIterMut.next it with
  | ok value =>
    rcases value with ⟨o,it1,nextBack⟩
    cases o with
    | none =>
      simp only [verifier.update_residue_row_loop1.body,h,bind_tc_ok]
      rfl
    | some limb =>
      simp only [verifier.update_residue_row_loop1.body,h,bind_tc_ok]
      change (do let y ← foldWord limb
                 ok (cont (it1,fun im => back (nextBack im (some y))))) = _
      rw [fold_eq,bind_tc_ok]
      rfl
  | fail e => simp only [verifier.update_residue_row_loop1.body,h,bind_tc_fail]
  | div => simp only [verifier.update_residue_row_loop1.body,h,bind_tc_div]


#print axioms toK
#print axioms row_four
#print axioms add_unroll
#print axioms range_next
#print axioms owned_four
#print axioms fold_body_complete
end Port26ROW
end
