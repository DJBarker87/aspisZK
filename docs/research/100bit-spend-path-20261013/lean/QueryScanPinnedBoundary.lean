import ExtractedOpeningQueriesModel

/-! A countermodel at the actual pinned query decoder boundary. A theorem over
free B.decode cannot establish distinctness or the scan-selected state. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.QueryScanPinnedBoundary

 def arbitraryBoundary (queries : Array U32 22#usize) (state : Array U8 32#usize) :
    QueriesModel.Boundaries where
   decode := fun _ _ => ok (.Ok (queries, state))
   embed := fun _ => .fail .panic

 theorem arbitrary_output (queries : Array U32 22#usize) (state : Array U8 32#usize)
    (blocks advances : Array (Array U8 32#usize) 8#usize) :
    (arbitraryBoundary queries state).decode blocks advances = ok (.Ok (queries, state)) := rfl

 theorem duplicate_output_possible
    (state : Array U8 32#usize) (blocks advances : Array (Array U8 32#usize) 8#usize) :
    ∃ B : QueriesModel.Boundaries,
      B.decode blocks advances = ok (.Ok (Array.repeat 22#usize 0#u32, state)) :=
    ⟨arbitraryBoundary _ state, rfl⟩

 theorem selected_state_unconstrained
    (queries : Array U32 22#usize) (s t : Array U8 32#usize)
    (blocks advances : Array (Array U8 32#usize) 8#usize) :
    (arbitraryBoundary queries s).decode blocks advances = ok (.Ok (queries, s)) ∧
    (arbitraryBoundary queries t).decode blocks advances = ok (.Ok (queries, t)) := ⟨rfl, rfl⟩

#print axioms arbitrary_output
#print axioms duplicate_output_possible
#print axioms selected_state_unconstrained
end AspisR1PublicPreparation.QueryScanPinnedBoundary
