import S1ValuesOwnedExactV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result

/-- The same installed leaf success derives its own dimensions and exact
bytes. There is no independent alignment, output-size or loop premise. -/
theorem accepted_bytes (input output updated : Slice U8)
    (call : expandValues input output=ok (.Ok (),updated)) :
    updated.length=output.length ∧ output.length=2*input.length ∧ input.length%16=0 ∧
    ∀ j, j<updated.length → updated.val[j]?=
      if j%32<16 then input.val[(j/32)*16+j%32]? else some 0#u8 := by
  unfold expandValues at call
  cases source : AspisS1ValuesOwned.values_owned_reference (toVec input) (toVec output) with
  | fail e => simp only [source] at call;cases call
  | div => simp only [source] at call;cases call
  | ok result =>
    rcases result with ⟨status,next,out⟩
    simp only [source,bind_tc_ok] at call
    have pair : (status,toSlice out)=(.Ok (),updated) := Result.ok.inj call
    have sameStatus : status=.Ok () := congrArg Prod.fst pair
    have sameOutput : toSlice out=updated := congrArg Prod.snd pair
    subst status
    subst updated
    obtain ⟨_,length,shape,aligned,bytes⟩ :=
      AspisS1ValuesOwnedReferenceBytes.reference_bytes _ _ _ _ source
    exact ⟨length,shape,aligned,bytes⟩

#print axioms accepted_bytes
end AspisS1ValuesOwnedInstallation
