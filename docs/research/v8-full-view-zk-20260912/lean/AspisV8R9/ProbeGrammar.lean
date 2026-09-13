import AspisV8PairedCommitment.Domains
import Mathlib.Data.List.Basic

/-! One fixed-width suffix candidate per eligible query. Only the displayed
byte families are excluded; no claim is made about uninspected SHA call sites,
adversary calls, or the complete generated source. -/
set_option autoImplicit false
namespace AspisV8R9
open AspisV8PairedCommitment

theorem suffix_of_leaf_input (tag : Byte) (packed salt : List Byte) :
    (leafInput tag packed salt).drop (2 + packed.length) = salt := by
  change ((16 : Byte) :: tag :: packed ++ salt).drop (2 + packed.length) = salt
  have prefixLength : ((16 : Byte) :: tag :: packed).length = 2 + packed.length := by
    simp only [List.length_cons]
    omega
  rw [← prefixLength, List.drop_left]

theorem one_query_has_one_salt (input packedLeft packedRight saltLeft saltRight : List Byte)
    (tagLeft tagRight : Byte)
    (first : input = leafInput tagLeft packedLeft saltLeft)
    (second : input = leafInput tagRight packedRight saltRight)
    (sameWidth : packedLeft.length = packedRight.length) :
    saltLeft = saltRight := by
  calc
    saltLeft = (leafInput tagLeft packedLeft saltLeft).drop
        (2 + packedLeft.length) := (suffix_of_leaf_input _ _ _).symm
    _ = input.drop (2 + packedLeft.length) := congrArg
        (fun x : List Byte => x.drop (2 + packedLeft.length)) first.symm
    _ = (leafInput tagRight packedRight saltRight).drop
        (2 + packedLeft.length) := congrArg
          (fun x : List Byte => x.drop (2 + packedLeft.length)) second
    _ = (leafInput tagRight packedRight saltRight).drop
        (2 + packedRight.length) := by rw [sameWidth]
    _ = saltRight := suffix_of_leaf_input _ _ _

/-- ASCII `a` is 97; the inspected expander/derivation families start with
this byte, whereas every private leaf starts with 16. -/
theorem ascii_domain_not_leaf (tail packed salt : List Byte) (tag : Byte) :
    (97 : Byte) :: tail ≠ leafInput tag packed salt := by
  change (97 : Byte) :: tail ≠ (16 : Byte) :: tag :: (packed ++ salt)
  intro same
  exact (by decide : (97 : Byte) ≠ (16 : Byte)) (List.cons.inj same).1

#print axioms suffix_of_leaf_input
#print axioms one_query_has_one_salt
#print axioms ascii_domain_not_leaf
end AspisV8R9
