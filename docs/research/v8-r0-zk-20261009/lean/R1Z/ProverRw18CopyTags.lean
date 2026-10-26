import R0P.CopyRegistry
import R1Z.ProverRw18FieldInitial
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopyTags
open Aeneas Aeneas.Std

theorem range (link : R0P.CopyLink) (member : link ∈ R0P.copyLinks) :
    ∃ i : Nat, i<136 ∧ link.tag=1124073472+i := by
  have mapped : link.tag ∈ R0P.copyLinks.map R0P.CopyLink.tag := List.mem_map.mpr ⟨link,member,rfl⟩
  rw [R0P.copy_tags_indexed] at mapped
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp mapped
  exact ⟨i,List.mem_range.mp hi,eq.symm⟩

theorem canonical (link : R0P.CopyLink) (member : link ∈ R0P.copyLinks) :
    link.tag<2147483647 := by
  obtain ⟨i,hi,eq⟩ := range link member
  omega

def word (link : R0P.CopyLink) (member : link ∈ R0P.copyLinks) : U32 :=
  UScalar.ofNatCore link.tag (by
    have bound := canonical link member
    change link.tag<2^32
    omega)

theorem word_val (link : R0P.CopyLink) (member : link ∈ R0P.copyLinks) :
    (word link member).val=link.tag := rfl

theorem word_canonical (link : R0P.CopyLink) (member : link ∈ R0P.copyLinks) :
    (word link member).val<2147483647 := canonical link member

#print axioms range
#print axioms canonical
#print axioms word_val
#print axioms word_canonical
end R1Z.ProverRw18CopyTags
