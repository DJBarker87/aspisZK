import RPz7_PSem_Expansion
import RPz7_PSem_Root
import MultiproofConeByteEquality
set_option autoImplicit false
namespace AspisR1.PSem_ExpansionUnique
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open MultiproofConeCanonical

theorem bytes_unique (input initial1 initial2 output1 output2 : Slice U8)
    (first : compact.expand_semantic nativeValues input initial1=ok (.Ok (),output1))
    (second : compact.expand_semantic nativeValues input initial2=ok (.Ok (),output2)) :
    output1.val=output2.val := by
  obtain ⟨rows1,expanded1,suffix1⟩ := PSem_Expansion.source_rows input initial1 output1 first
  obtain ⟨rows2,expanded2,suffix2⟩ := PSem_Expansion.source_rows input initial2 output2 second
  have sameRows : rows1=rows2 := Option.some.inj (expanded1.symm.trans expanded2)
  have sameSuffix : output1.val.drop 32=output2.val.drop 32 := by
    apply MultiproofConeByteEquality.bytes_injective
    rw [suffix1,suffix2,sameRows]
  have prefix1 := PSem_Root.take_of_prefix input output1
    (AspisS1NativeCompactBodyFrame.semantic_root_prefix nativeValues input initial1 output1 first)
  have prefix2 := PSem_Root.take_of_prefix input output2
    (AspisS1NativeCompactBodyFrame.semantic_root_prefix nativeValues input initial2 output2 second)
  calc
    output1.val = output1.val.take 32 ++ output1.val.drop 32 := (List.take_append_drop 32 _).symm
    _ = output2.val.take 32 ++ output2.val.drop 32 := by rw [prefix1,prefix2,sameSuffix]
    _ = output2.val := List.take_append_drop 32 _

/-- Full successful expansion is independent of its initial destination
contents. Equality is derived for the complete returned slice carrier. -/
theorem carrier_unique (input initial1 initial2 output1 output2 : Slice U8)
    (first : compact.expand_semantic nativeValues input initial1=ok (.Ok (),output1))
    (second : compact.expand_semantic nativeValues input initial2=ok (.Ok (),output2)) :
    output1=output2 := by
  have same := bytes_unique input initial1 initial2 output1 output2 first second
  cases output1
  cases output2
  cases same
  rfl

#print axioms bytes_unique
#print axioms carrier_unique
end AspisR1.PSem_ExpansionUnique
