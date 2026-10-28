import NBR_AppendInduction
import NBL_ViewDomains
set_option autoImplicit false
namespace AspisR1.NCA_AppendDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- The actual selected view establishes BOTH native append-loop capacity
invariants. No per-iteration spare-capacity premise is supplied. -/
theorem source (proof semantic y1 : Slice U8) (full : proof.val.length=57607)
    (view : AspisR1SelectedWideViewV1.verifier.View)
    (call : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok view)) :
    ∃ root : Array U8 32#usize, view.folded_root=some root ∧
      (∀ i, i<root.val.length → (root.val.take i).length=i ∧ i<256 ∧ i+(32-i)≤256) ∧
      (∀ i, i<view.round1.val.length →
        (root.val++view.round1.val.take i).length=32+i ∧
        32+i<256 ∧ 32+i+(224-i)=256) := by
  obtain ⟨_,_,_,_,roundSize,_,root,rootCall,_⟩ :=
    NBL_ViewDomains.source proof semantic y1 full view call
  refine ⟨root,rootCall,?_,?_⟩
  · intro i bound
    have size : root.val.length=32 := root.property
    obtain ⟨length,capacity⟩ := NBR_AppendInduction.capacity ([] : List U8) root.val i
      (by simp only [List.length_nil,zero_add,size];omega) bound
    simp only [List.nil_append,List.length_nil,zero_add] at length capacity
    exact ⟨length,by rw [length] at capacity;exact capacity,by omega⟩
  · intro i bound
    have size : root.val.length=32 := root.property
    obtain ⟨length,capacity⟩ := NBR_AppendInduction.capacity root.val view.round1.val i
      (by rw [size,roundSize]) bound
    rw [size] at length
    refine ⟨length,?_,?_⟩
    · rwa [length] at capacity
    · omega

#print axioms source
end AspisR1.NCA_AppendDomain
