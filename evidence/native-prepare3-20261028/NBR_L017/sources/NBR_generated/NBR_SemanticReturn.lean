import JFw_Entry
import PSem_Expansion
import S1NativeCompactEntryLengthV1
set_option autoImplicit false
namespace AspisR1.NBR_SemanticReturn
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation MultiproofConeCanonical

/-- Existing semantic expansion constructs its output and all frozen rows
for every source/initial-buffer pair in the exact prepare domain. -/
theorem source (input initial : Slice U8)
    (inputLength : input.val.length=7015) (initialLength : initial.val.length=13831) :
    ∃ output : Slice U8,
      compact.expand_semantic nativeValues input initial=ok (.Ok (),output) ∧
      output.val.length=13831 ∧
      ∃ rows : List Bytes,
        PSem_Rows.expandRows 27 0 (bytesOf (input.val.drop 32))=some rows ∧
        bytesOf (output.val.drop 32)=rows.flatten := by
  obtain ⟨output,call⟩ := JFw_Entry.success input initial inputLength initialLength
  have length := AspisS1NativeCompactLengths.semantic_length nativeValues input initial output (.Ok ()) call
  exact ⟨output,call,length.trans initialLength,PSem_Expansion.source_rows input initial output call⟩

/-- The complete callee return already fixes this output and these rows.
No caller-chosen row list, output length or expansion success is invented. -/
theorem returned (input initial output : Slice U8)
    (initialLength : initial.val.length=13831)
    (call : compact.expand_semantic nativeValues input initial=ok (.Ok (),output)) :
    output.val.length=13831 ∧
      ∃ rows : List Bytes,
        PSem_Rows.expandRows 27 0 (bytesOf (input.val.drop 32))=some rows ∧
        bytesOf (output.val.drop 32)=rows.flatten := by
  exact ⟨(AspisS1NativeCompactLengths.semantic_length nativeValues input initial output (.Ok ()) call).trans
    initialLength,PSem_Expansion.source_rows input initial output call⟩

#print axioms source
#print axioms returned
end AspisR1.NBR_SemanticReturn
