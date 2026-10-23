import S2SdkProofGateModelV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisS2OwnedStage1.SdkReference.ProofGate

abbrev CellEq (bytes candidate : Slice U8) (index : Nat) : Prop :=
  bytes.val[index]?=candidate.val[index]?

private theorem add_total (a : Usize) (h : a.val+1≤Usize.max) :
    ∃ next : Usize,(a+1#usize : Result Usize)=ok next ∧ next.val=a.val+1 := by
  apply WP.spec_imp_exists
  apply UScalar.add_spec
  rw [UScalar.max_USize_eq]
  exact h

theorem prefix_step (bytes candidate : Slice U8) (offset : Usize)
    (long : candidate.val.length≤bytes.val.length)
    (valid : offset.val<candidate.val.length) :
    ∃ next : Usize,next.val=offset.val+1 ∧
      prefix_different_loop.body bytes candidate offset=
        ok (if CellEq bytes candidate offset.val then cont next else done (some true)) := by
  have validBytes : offset.val<bytes.val.length := by omega
  obtain ⟨left,hleft,leftCell⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec bytes offset validBytes)
  obtain ⟨right,hright,rightCell⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec candidate offset valid)
  have bound : candidate.val.length≤Usize.max := candidate.property
  obtain ⟨next,hnext,value⟩ := add_total offset (by omega)
  have condition : offset<Slice.len candidate := valid
  have equal : CellEq bytes candidate offset.val ↔ left=right := by
    unfold CellEq
    rw [List.getElem?_eq_getElem validBytes,List.getElem?_eq_getElem valid,
      ←leftCell,←rightCell]
    exact ⟨Option.some.inj,congrArg some⟩
  refine ⟨next,value,?_⟩
  by_cases same : left=right
  · have cells := equal.mpr same
    simp [prefix_different_loop.body,condition,hleft,hright,same,hnext,cells]
  · have cells : ¬CellEq bytes candidate offset.val := fun h => same (equal.mp h)
    have unequal : left.val≠right.val := fun h => same (UScalar.eq_of_val_eq h)
    simp [prefix_different_loop.body,condition,hleft,hright,unequal,cells]

/-- TOTAL at every representable slice length, with exact first-mismatch
semantics. No successful read, increment or loop execution is a premise. -/
theorem prefix_total (bytes candidate : Slice U8) :
    ∃ out : Bool,prefix_different bytes candidate=ok out ∧
      (out=false ↔ candidate.val.length≤bytes.val.length ∧
        ∀ j,j<candidate.val.length → CellEq bytes candidate j) := by
  by_cases short : bytes.val.length<candidate.val.length
  · refine ⟨true,?_,?_⟩
    · have condition : Slice.len bytes<Slice.len candidate := short
      simp only [prefix_different,if_pos condition]
    · constructor
      · intro h; cases h
      · intro h; omega
  · have long : candidate.val.length≤bytes.val.length := by omega
    let allEq := ∀ j,j<candidate.val.length → CellEq bytes candidate j
    have spec : WP.spec (prefix_different_loop bytes candidate 0#usize)
        (fun out => (out=none ↔ allEq) ∧ (out=none ∨ out=some true)) := by
      unfold prefix_different_loop
      refine loop.spec_decr_nat (fun i : Usize => candidate.val.length-i.val)
        (fun i => i.val≤candidate.val.length ∧ ∀ j : Nat, j < i.val → CellEq bytes candidate j)
        (fun out => (out=none ↔ allEq) ∧ (out=none ∨ out=some true))
        (fun i => prefix_different_loop.body bytes candidate i) 0#usize ?_ ?_
      · intro i invariant
        rcases invariant with ⟨bound,previous⟩
        by_cases valid : i.val<candidate.val.length
        · obtain ⟨next,value,step⟩ := prefix_step bytes candidate i long valid
          by_cases equal : CellEq bytes candidate i.val
          · rw [step,if_pos equal,WP.spec_ok]
            constructor
            · refine ⟨by omega,?_⟩
              intro j before
              by_cases last : j=i.val
              · subst j; exact equal
              · exact previous j (by omega)
            · omega
          · rw [step,if_neg equal,WP.spec_ok]
            refine ⟨?_,Or.inr rfl⟩
            constructor
            · intro h; cases h
            · intro all; exact False.elim (equal (all i.val valid))
        · have condition : ¬i<Slice.len candidate := valid
          simp only [prefix_different_loop.body,if_neg condition,WP.spec_ok]
          refine ⟨?_,Or.inl trivial⟩
          constructor
          · intro _ j hj; exact previous j (by omega)
          · intro _; trivial
      · exact ⟨by change (0:Nat)≤candidate.val.length; omega,
          by intro j hj; change j<(0:Nat) at hj; omega⟩
    obtain ⟨out,run,equal,cases⟩ := WP.spec_imp_exists spec
    have condition : ¬Slice.len bytes<Slice.len candidate := short
    cases cases with
    | inl none =>
      subst out
      refine ⟨false,?_,?_⟩
      · simp only [prefix_different,if_neg condition,run,bind_tc_ok]
      · exact ⟨fun _ => ⟨long,equal.mp rfl⟩,fun _ => rfl⟩
    | inr hit =>
      subst out
      refine ⟨true,?_,?_⟩
      · simp only [prefix_different,if_neg condition,run,bind_tc_ok]
      · constructor
        · intro h; cases h
        · intro h; have contradiction := equal.mpr h.2; cases contradiction

#print axioms prefix_step
#print axioms prefix_total
end AspisS2OwnedStage1.SdkReference.ProofGate
