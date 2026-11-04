import NFQ_PreparedMultiplier
set_option autoImplicit false
namespace NFQ_PreparedDomain
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedMaskTowerAdd
open NFQ_PreparedMultiplier

theorem spec_canonical (x : Q) (h : CanonicalQM x) :
 ∀ row ∈ spec x, ∀ word ∈ row, word<2147483647 := by
 intro row hr word hw
 simp only [spec,List.mem_cons,List.not_mem_nil,or_false] at hr
 rcases hr with rfl | rfl | rfl
 all_goals
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl
  all_goals first | exact h.1.1 | exact h.1.2 | exact h.2.1 | exact h.2.2 | exact Nat.mod_lt _ (by decide)

theorem output_domain (x : Q) (h : CanonicalQM x) :
 ∃ out : Prepared, AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new x=ok out ∧
   (∀ row ∈ words out, ∀ word ∈ row,word<2147483647) := by
 obtain ⟨out,run,eq⟩:=NFQ_PreparedMultiplier.source x h
 exact ⟨out,run,eq.symm ▸ spec_canonical x h⟩
#print axioms spec_canonical
#print axioms output_domain
end NFQ_PreparedDomain
