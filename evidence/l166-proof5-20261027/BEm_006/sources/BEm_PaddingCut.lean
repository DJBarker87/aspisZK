import BEm_PaddingModel
set_option autoImplicit false
namespace AspisR1.BEm_PaddingCut
open BEm_PaddingModel

/-- Arbitrarily long whole-word scans, including empty suffixes. The actual
byte-slice/chunks iterator association is deliberately outside this model law. -/
theorem cut (words : List Word) (validWords : ∀ w ∈ words, valid w) (count : Nat) :
    (words.drop (4*count)).any nativeWord =
      ((words.drop (4*count)).flatMap bytes).any (fun b => decide (b≠0)) := by
  apply traversal
  intro w member
  exact validWords w (List.mem_of_mem_drop member)

theorem domain (words : List Word) (capacity count : Nat)
    (shape : words.length=4*capacity) (guard : count≤capacity) (bounded : capacity≤172) :
    (words.drop (4*count)).length≤688 ∧ 32*count≤32*capacity ∧
      32*capacity≤5504 ∧ (32*capacity-32*count)%8=0 := by
  have geometry := BEl_GateBounds.padding_domain count capacity guard bounded
  refine ⟨?_,geometry⟩
  rw [List.length_drop,shape]
  omega

#print axioms cut
#print axioms domain
end AspisR1.BEm_PaddingCut
