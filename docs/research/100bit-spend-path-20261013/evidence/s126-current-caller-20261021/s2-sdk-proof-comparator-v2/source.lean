import S2SdkProofPrefixTotalV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ProofGate

private theorem u8_ne (left right : U8) :
    core.cmp.PartialEqU8.ne left right=ok (decide (left≠right)) := by
  simp

private theorem lists_ne (left right : List U8) :
    (if left.length=right.length then
      List.anyM (fun pair : U8×U8 => ok (decide (pair.1≠pair.2)))
        (left.zip right)
      else ok true)=ok (decide (left≠right)) := by
  induction left generalizing right with
  | nil => cases right <;> simp <;> rfl
  | cons a rest ih =>
    cases right with
    | nil => simp
    | cons b tail =>
      by_cases length : rest.length=tail.length
      · have tailEq := ih tail
        simp only [if_pos length] at tailEq
        simp only [List.length_cons,Nat.add_right_cancel_iff,length,if_true,
          List.zip_cons_cons,List.anyM_cons,bind_tc_ok]
        rw [tailEq]
        by_cases same : a=b
        · subst b; simp
        · simp [same]
      · have unequal : a::rest≠b::tail := by
          intro equal
          have lengths := congrArg List.length equal
          simp only [List.length_cons] at lengths
          omega
        simp [length,unequal]

theorem standard_ne (left right : Slice U8) :
    core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8 left right=
      ok (decide (left.val≠right.val)) := by
  unfold core.slice.cmp.PartialEqSlice.ne
  have predicate : (fun pair : U8×U8 => core.cmp.PartialEqU8.ne pair.1 pair.2)=
      (fun pair => ok (decide (pair.1≠pair.2))) := by
    funext pair
    exact u8_ne pair.1 pair.2
  rw [predicate]
  exact lists_ne left.val right.val

def scalarNe (left right : Slice U8) : Result Bool :=
  if left.val.length=right.val.length then prefix_different left right else ok true

/-- Exact scalar loop binding of the installed U8 slice comparator, all lengths. -/
theorem scalarNe_eq_standard (left right : Slice U8) :
    scalarNe left right=core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8 left right := by
  rw [standard_ne]
  unfold scalarNe
  by_cases length : left.val.length=right.val.length
  · rw [if_pos length]
    obtain ⟨different,run,semantics⟩ := prefix_total left right
    rw [run]
    have equivalent : (left.val=right.val) ↔
        ∀ j,j<right.val.length → CellEq left right j := by
      constructor
      · intro same j _; simp only [CellEq,same]
      · intro same
        apply List.ext_getElem?
        intro j
        by_cases valid : j<right.val.length
        · exact same j valid
        · have l : left.val[j]?=none := List.getElem?_eq_none (by omega)
          have r : right.val[j]?=none := List.getElem?_eq_none (by omega)
          rw [l,r]
    cases different with
    | false =>
      have all := (semantics.mp rfl).2
      have same := equivalent.mpr all
      simp [same]
    | true =>
      have unequal : left.val≠right.val := by
        intro same
        have contradiction := semantics.mpr ⟨by omega,equivalent.mp same⟩
        cases contradiction
      simp [unequal]
  · rw [if_neg length]
    have unequal : left.val≠right.val := fun h => length (congrArg List.length h)
    simp [unequal]

#print axioms standard_ne
#print axioms scalarNe_eq_standard
end AspisS2OwnedStage1.SdkReference.ProofGate
