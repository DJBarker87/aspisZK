import S2SdkGateAdmittedImageV1
import S2SdkProofGateJoinV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ProofGate

/-- The exact three reached native-shaped caller guard operations imply the
full-buffer reference gate result. Range/comparator/tag equality are tied to
one original Vec and candidate, never to separately selected byte carriers. -/
theorem caller_guard (proof : alloc.vec.Vec U8) (candidate : Array U8 688#usize)
    (selected : Slice U8) (length : proof.val.length=58295)
    (range : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      proof {«end»:=688#usize}=ok selected)
    (compared : ProofPrefixParent.loopCmp selected candidate=ok false)
    (tag : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8)
      proof 696#usize=ok 2#u8) :
    reference_gate (alloc.vec.Vec.deref proof) candidate=
      ok (core.result.Result.Ok (688#usize,58295#usize)) := by
  obtain ⟨same,actualRange,cmp⟩ := caller_prefix_eq proof candidate length
  have sameSelected : same=selected := Result.ok.inj (actualRange.symm.trans range)
  subst same
  have prefixRun := cmp.trans compared
  have sum : (688#usize+57607#usize : Result Usize)=ok 58295#usize := by
    apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
  have checked : Usize.checked_add 688#usize 57607#usize=some 58295#usize := by
    unfold Usize.checked_add core.num.checked_add_UScalar
    rw [sum]; rfl
  have offset : (688#usize+8#usize : Result Usize)=ok 696#usize := by
    apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
  have lengthSlice : Slice.len (alloc.vec.Vec.deref proof)=58295#usize := by
    apply UScalar.eq_of_val_eq
    simpa [Slice.len,FrameOperationsTotal.deref_val] using length
  change Slice.index_usize (alloc.vec.Vec.deref proof) 696#usize=ok 2#u8 at tag
  simp [reference_gate,checked,lift,SourceInstallation.stdOption,
    core.result.Result.Insts.CoreOpsTry.branch,lengthSlice,prefixRun,offset,tag]

#print axioms caller_guard
end AspisS2OwnedStage1.SdkReference.ProofGate
