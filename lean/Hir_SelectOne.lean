import Hir_WriterSelect
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_SelectOne
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect
variable {A : Type} (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (key : Nat) (data : Slice U8)

theorem sound (site : CallAt A) (writer : Writer A)
    (selected : one native1 copy allocator id key data site = some writer) :
    writer.site = site ∧
      first native1 copy allocator (load writer.site.before writer.site.call.layout) id writer.site.call.data writer.site.call.state =
        ok (.Ok (writer.saved,writer.post,writer.final)) ∧
      Hiq_ReleaseRoute.route writer.site.call.data = .first ∧
      (writer.site.call.layout.handles 2).1 = key ∧ data = writer.saved.deref := by
  classical
  unfold one at selected
  split at selected
  · rename_i guards
    cases actual : first native1 copy allocator (load site.before site.call.layout) id site.call.data site.call.state with
    | fail e => simp only [actual] at selected; cases selected
    | div => simp only [actual] at selected; cases selected
    | ok result => cases result with
      | Err e => simp only [actual] at selected; cases selected
      | Ok value =>
        rcases value with ⟨saved,post,final⟩
        simp only [actual] at selected
        split at selected
        · rename_i equal
          have eq := Option.some.inj selected
          subst writer
          exact ⟨rfl,actual,guards.1,guards.2,equal⟩
        · cases selected
  · cases selected

theorem complete (site : CallAt A) (birth : Birth native1 copy allocator id key data site) :
    ∃ writer, one native1 copy allocator id key data site = some writer := by
  classical
  obtain ⟨route,address,saved,post,final,accepted,equal⟩ := birth
  exact ⟨⟨site,saved,post,final⟩,by simp only [one,if_pos (And.intro route address),accepted,if_pos equal]⟩

#print axioms sound
#print axioms complete
end AspisR1.Hir_SelectOne
end
