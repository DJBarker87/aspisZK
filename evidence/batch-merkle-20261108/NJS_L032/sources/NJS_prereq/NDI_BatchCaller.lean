import NDI_BatchBridge
set_option autoImplicit false
namespace NDI_BatchCaller
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem canonical (p : verifier.Prepared) (a : verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am) :
    ∀ k, k<22 → p.queries.val[k]!.val<262144 := by
  intro k bound
  have len : p.queries.val.length=22 := p.queries.property
  have cell := congrArg (fun xs : List Nat => xs[k]!) fields.queries
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem (by omega : k<p.queries.val.length),Option.map_some,
    Option.getD_some,List.getElem?_ofFn,bound,↓reduceDIte] at cell
  have value : p.queries.val[k]!.val=(pm.queries ⟨k,bound⟩).val := by
    simpa only [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : k<p.queries.val.length),Option.getD_some] using cell
  rw [value]
  exact (pm.queries ⟨k,bound⟩).isLt

#print axioms canonical
end NDI_BatchCaller
