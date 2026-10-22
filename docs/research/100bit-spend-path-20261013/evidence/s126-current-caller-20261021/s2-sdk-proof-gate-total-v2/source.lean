import S2SdkProofPrefixTotalV1
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

/-- TOTAL at every representable proof length. All invalid lengths reject before
prefix traversal; a correct length derives the tag index's own validity. -/
theorem gate_total (proof : Slice U8) (candidate : Array U8 688#usize) :
    ∃ out,reference_gate proof candidate=ok out ∧
      (out=core.result.Result.Ok (688#usize,58295#usize) ∨
       out=core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData) := by
  unfold reference_gate
  simp only [checked_end,lift,bind_tc_ok,SourceInstallation.stdOption,
    core.result.Result.Insts.CoreOpsTry.branch]
  by_cases length : Slice.len proof=58295#usize
  · have lenVal : proof.val.length=58295 := by
      have value := congrArg UScalar.val length
      simpa [Slice.len] using value
    simp [length]
    obtain ⟨different,run,_⟩ := prefix_total proof (Array.to_slice candidate)
    rw [run]
    simp only [bind_tc_ok]
    cases different with
    | true => exact ⟨_,rfl,Or.inr rfl⟩
    | false =>
      simp only [Bool.false_eq_true,if_false,tag_offset,bind_tc_ok]
      obtain ⟨byte,read,_⟩ := WP.spec_imp_exists
        (Slice.index_usize_spec proof 696#usize (by scalar_tac))
      rw [read]
      simp only [bind_tc_ok]
      by_cases tag : byte=2#u8
      · refine ⟨_,?_,Or.inl rfl⟩
        simp [tag]
      · have value : byte.val≠2 := fun h => tag (UScalar.eq_of_val_eq h)
        refine ⟨_,?_,Or.inr rfl⟩
        simp [tag,value]
  · have value : (Slice.len proof).val≠58295 := fun h => length (UScalar.eq_of_val_eq h)
    refine ⟨_,?_,Or.inr rfl⟩
    simp [length,value]

#print axioms gate_total
#print core.slice.cmp.PartialEqSlice.eq
#print core.slice.cmp.PartialEqSlice.ne
end AspisS2OwnedStage1.SdkReference.ProofGate
