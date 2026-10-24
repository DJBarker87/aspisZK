import S2SdkProofGateTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ProofGate

private theorem checked_end :
    Usize.checked_add 688#usize 57607#usize=some 58295#usize := by
  have sum : (688#usize+57607#usize : Result Usize)=ok 58295#usize := by
    apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
  unfold Usize.checked_add core.num.checked_add_UScalar
  rw [sum]
  rfl

private theorem tag_offset : (688#usize+8#usize : Result Usize)=ok 696#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac

/-- ACCEPTED-ONLY, for the actual extracted gate. Its successful return derives
all initializer fixed-point conditions; byte equality is not an extra premise. -/
theorem admitted_cells (proof : Slice U8) (candidate : Array U8 688#usize)
    (accepted : reference_gate proof candidate=ok (core.result.Result.Ok (688#usize,58295#usize))) :
    proof.val.length=58295 ∧
    (∀ j,j<688 → CellEq proof (Array.to_slice candidate) j) ∧
    proof.val[696]?=some 2#u8 := by
  have length : Slice.len proof=58295#usize := by
    by_contra wrong
    rw [wrong_length_reject proof candidate wrong] at accepted
    cases accepted
  have lenVal : proof.val.length=58295 := by
    have value := congrArg UScalar.val length
    simpa [Slice.len] using value
  refine ⟨lenVal,?_⟩
  unfold reference_gate at accepted
  simp only [checked_end,lift,bind_tc_ok,SourceInstallation.stdOption,
    core.result.Result.Insts.CoreOpsTry.branch] at accepted
  simp [length] at accepted
  obtain ⟨different,run,spec⟩ := prefix_total proof (Array.to_slice candidate)
  rw [run] at accepted
  simp only [bind_tc_ok] at accepted
  cases different with
  | true => simp at accepted
  | false =>
    have cells :=  (spec.mp rfl).2
    have prefix688 : ∀ j,j<688 → CellEq proof (Array.to_slice candidate) j := by
      intro j valid
      apply cells j
      simpa [Array.to_slice] using valid
    refine ⟨prefix688,?_⟩
    simp only [Bool.false_eq_true,if_false,tag_offset,bind_tc_ok] at accepted
    obtain ⟨byte,read,cell⟩ := WP.spec_imp_exists
      (Slice.index_usize_spec proof 696#usize (by scalar_tac))
    rw [read] at accepted
    simp only [bind_tc_ok] at accepted
    have tag : byte=2#u8 := by
      by_contra wrong
      have unequal : byte.val≠2 := fun h => wrong (UScalar.eq_of_val_eq h)
      simp [unequal] at accepted
    change byte=proof.val[696] at cell
    rw [List.getElem?_eq_getElem (by omega : 696<proof.val.length)]
    exact congrArg some (cell.symm.trans tag)

/-- The exact pointwise prefix/tag initializer image. Outside the written
prefix and tag cell it retains the original byte, including invalid indices. -/
def seedCell (proof : Slice U8) (candidate : Array U8 688#usize) (j : Nat) : Option U8 :=
  if j<688 then (Array.to_slice candidate).val[j]?
  else if j=696 then some 2#u8 else proof.val[j]?

/-- Every gate-admitted proof is a fixed point of the native harness initializer
at every coordinate. This is full byte equality, including rejected suffixes;
no child decoder, verifier success, oracle, or hidden equality premise. -/
theorem admitted_seed_fixed (proof : Slice U8) (candidate : Array U8 688#usize)
    (accepted : reference_gate proof candidate=ok (core.result.Result.Ok (688#usize,58295#usize)))
    (j : Nat) : seedCell proof candidate j=proof.val[j]? := by
  obtain ⟨_,cells,tag⟩ := admitted_cells proof candidate accepted
  unfold seedCell
  split
  · exact (cells j (by assumption)).symm
  · split
    · subst j; exact tag.symm
    · rfl

#print axioms admitted_cells
#print axioms admitted_seed_fixed
end AspisS2OwnedStage1.SdkReference.ProofGate
