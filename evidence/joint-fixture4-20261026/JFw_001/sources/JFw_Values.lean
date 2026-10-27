import S1ValuesOwnedExactV1
import PSem_Values
set_option autoImplicit false
namespace AspisR1.JFw_Values
open Aeneas Aeneas.Std Result WP
open AspisS1ValuesOwnedInstallation

/-- Forward success of the actual installed values leaf, from dimensions alone. -/
theorem success (input output : Slice U8)
    (aligned : input.length % 16 = 0) (shape : output.length = 2*input.length)
    (doubling : 2*input.length ≤ Usize.max) :
    ∃ updated, expandValues input output = ok (.Ok (),updated) ∧
      updated.length = output.length ∧
      MultiproofConeCanonical.bytesOf updated.val =
        OraclePortCompactDraft.expand (input.length/16)
          (MultiproofConeCanonical.bytesOf input.val) := by
  obtain ⟨updated,call,length,_⟩ :=
    AspisS1ValuesOwnedExact.installed_exact input output aligned shape doubling
  exact ⟨updated,call,length,PSem_Values.source_expansion input output updated call⟩

@[step] theorem spec (input output : Slice U8)
    (aligned : input.length % 16 = 0) (shape : output.length = 2*input.length)
    (doubling : 2*input.length ≤ Usize.max) :
    expandValues input output ⦃ result => result.1 = .Ok () ∧
      result.2.length = output.length ⦄ := by
  obtain ⟨updated,call,length,_⟩ := success input output aligned shape doubling
  rw [call]
  exact ⟨rfl,length⟩

#print axioms success
#print axioms spec
end AspisR1.JFw_Values
