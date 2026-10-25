import Hir_SelectOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_Search
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect
variable {A : Type} (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (key : Nat) (data : Slice U8)

theorem sound (sites : List (CallAt A)) (writer : Writer A)
    (selected : search native1 copy allocator id key data sites = some writer) :
    writer.site ∈ sites ∧ Birth native1 copy allocator id key data writer.site ∧
      first native1 copy allocator (load writer.site.before writer.site.call.layout) id writer.site.call.data writer.site.call.state =
        ok (.Ok (writer.saved,writer.post,writer.final)) ∧ data = writer.saved.deref := by
  induction sites with
  | nil => cases selected
  | cons site rest ih =>
    cases head : one native1 copy allocator id key data site with
    | some chosen =>
      have eq : chosen = writer := Option.some.inj (by simpa only [search,head] using selected)
      subst chosen
      obtain ⟨same,accepted,route,address,equal⟩ := Hir_SelectOne.sound native1 copy allocator id key data site writer head
      exact ⟨by rw [same]; exact List.mem_cons_self,
        ⟨route,address,writer.saved,writer.post,writer.final,accepted,equal⟩,accepted,equal⟩
    | none =>
      have tail : search native1 copy allocator id key data rest = some writer := by simpa only [search,head] using selected
      obtain ⟨member,birth,accepted,equal⟩ := ih tail
      exact ⟨List.mem_cons_of_mem _ member,birth,accepted,equal⟩

theorem complete (sites : List (CallAt A))
    (existsBirth : ∃ site ∈ sites, Birth native1 copy allocator id key data site) :
    ∃ writer, search native1 copy allocator id key data sites = some writer := by
  induction sites with
  | nil => rcases existsBirth with ⟨site,member,_⟩; cases member
  | cons site rest ih =>
    cases head : one native1 copy allocator id key data site with
    | some writer => exact ⟨writer,by simp only [search,head]⟩
    | none =>
      obtain ⟨chosen,member,birth⟩ := existsBirth
      rcases List.mem_cons.mp member with same | tail
      · subst chosen
        obtain ⟨writer,yes⟩ := Hir_SelectOne.complete native1 copy allocator id key data site birth
        rw [head] at yes
        cases yes
      · obtain ⟨writer,yes⟩ := ih ⟨chosen,tail,birth⟩
        exact ⟨writer,by simpa only [search,head] using yes⟩

#print axioms sound
#print axioms complete
end AspisR1.Hir_Search
end
