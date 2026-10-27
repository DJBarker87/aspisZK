import S1ValuesOwnedReferenceBytesV1
import S1ValuesOwnedInstallationV1
import S1ValuesOwnedOuterTotalV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedExact
open Aeneas Aeneas.Std Result WP AspisS1ValuesOwned
abbrev Buffer := alloc.vec.Vec U8

/-- TOTAL codec success on valid dimensions; both dimensions are public
metadata, not independent leaf-execution or loop witnesses. -/
theorem reference_success (input output : Buffer)
    (aligned : input.length%16=0) (shape : output.length=2*input.length)
    (doubling : 2*input.length ≤ Usize.max) :
    ∃ next updated, values_owned_reference input output=ok (.Ok (),next,updated) := by
  have hs : values_owned_reference input output ⦃ result => result.1=.Ok () ⦄ := by
    unfold values_owned_reference
    step* <;> scalar_tac
  obtain ⟨result,call,status⟩ := spec_imp_exists hs
  rcases result with ⟨status1,next,updated⟩
  change status1=.Ok () at status
  subst status1
  exact ⟨next,updated,call⟩

/-- The full installed reference satisfies the SAME byte formula checked on
the unchanged native function. This theorem does not encode Kani as an axiom. -/
theorem installed_exact (input output : Slice U8)
    (aligned : input.length%16=0) (shape : output.length=2*input.length)
    (doubling : 2*input.length ≤ Usize.max) :
    ∃ updated, AspisS1ValuesOwnedInstallation.expandValues input output=ok (.Ok (),updated) ∧
      updated.length=output.length ∧
      ∀ j, j<updated.length → updated.val[j]?=
        if j%32<16 then input.val[(j/32)*16+j%32]? else some 0#u8 := by
  obtain ⟨next,updated,call⟩ := reference_success
    (AspisS1ValuesOwnedInstallation.toVec input) (AspisS1ValuesOwnedInstallation.toVec output)
    aligned shape doubling
  obtain ⟨sameInput,sameLength,_,_,bytes⟩ :=
    AspisS1ValuesOwnedReferenceBytes.reference_bytes _ _ _ _ call
  refine ⟨AspisS1ValuesOwnedInstallation.toSlice updated,?_,sameLength,?_⟩
  · simp only [AspisS1ValuesOwnedInstallation.expandValues,call,bind_tc_ok]
    rfl
  · exact bytes

#print axioms reference_success
#print axioms installed_exact
end AspisS1ValuesOwnedExact
