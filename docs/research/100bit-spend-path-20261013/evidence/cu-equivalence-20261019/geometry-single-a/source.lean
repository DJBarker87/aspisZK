import CuSavingsGeometryCandidate7
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometrySingle
open Aeneas Aeneas.Std Result AspisR1GeometryCandidate7
open CuSavingsGeometryCandidate7 CuSavingsGeometryCaller CuSavingsGeometryFront

/-- Exact public single-query frame: checked next+1, geometry construction,
common inversion, then one query. The range guard is derived from the actual
successful checked addition; overflow and all constructor errors are shared. -/
theorem source_public_query_context {X A T : Type} (queries : Queries)
    (folds index : Usize)
    (prepare : Common→Result (core.result.Result X verifier.Error))
    (before : X→Result (core.result.Result A verifier.Error))
    (tail : M→A→Result T) (error : verifier.Error→Result T) :
    (do let finish ← index+1#usize
        let result ← new.front queries index finish
        match result with
        | .Err e => error e
        | .Ok front => do
          let prepared ← prepare (newView front)
          match prepared with
          | .Err e => error e
          | .Ok value => optimizedQuery queries folds index index front.line_z_values (before value) tail error)=
    (do let finish ← index+1#usize
        let result ← old.front queries index finish
        match result with
        | .Err e => error e
        | .Ok front => do
          let prepared ← prepare (oldView front)
          match prepared with
          | .Err e => error e
          | .Ok value => referenceQuery queries folds index (before value) tail error) := by
  apply (bind_eq_iff (index+1#usize : Result Usize) _ _).mpr
  intro finish hfinish
  have hs := UScalar.add_equiv index 1#usize
  rw [hfinish] at hs
  have hone : (1#usize).val=1 := by scalar_tac
  have guard : index<finish := by
    change index.val < finish.val
    have := hs.2.1
    omega
  exact source_caller_context queries folds index index finish (.initial) guard prepare before tail error

#print axioms source_public_query_context
end AspisR1.CuSavingsGeometrySingle
