import PSem_SemanticRows
set_option autoImplicit false
namespace AspisR1.PSem_Root
open Aeneas Aeneas.Std Result
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisS1NativeCompactBodyFrame

theorem take_of_prefix (input output : Slice U8) (h : Prefix 32 input output) :
    output.val.take 32=input.val.take 32 := by
  apply List.ext_getElem?
  intro j
  by_cases bound : j<32
  · simp only [List.getElem?_take,if_pos bound,h j bound]
  · simp only [List.getElem?_take,if_neg bound]

theorem source_root (input out expanded : Slice U8)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues input out=ok (.Ok (),expanded))
    (parse : AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    pre.c1_root.val=input.val.take 32 := by
  have prefix := semantic_root_prefix nativeValues input out expanded expand
  have root := (AspisR1.ExtractedPrefixParse.parse_success expanded
    (AspisR1PublicPreparation.PrefixAdapter.toOld pre)
    (AspisR1PublicPreparation.PrefixAdapter.parse_success expanded pre parse)).1
  exact root.trans (take_of_prefix input expanded prefix)

#print axioms take_of_prefix
#print axioms source_root
end AspisR1.PSem_Root
