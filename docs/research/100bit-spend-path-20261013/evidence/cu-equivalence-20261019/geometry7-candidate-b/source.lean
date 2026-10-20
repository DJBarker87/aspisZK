import CuSavingsGeometryFront
import CuSavingsGeometryDispatch
import CuSavingsGeometryCache
import CuSavingsGeometryCaller
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometryCandidate7
open Aeneas Aeneas.Std Result AspisR1GeometryCandidate7
open CuSavingsGeometryNode CuSavingsGeometryRow CuSavingsGeometryDispatch
open CuSavingsGeometryFront CuSavingsGeometryCaller
abbrev Queries := Array U32 22#usize

def queryAt (queries : Queries) (index : Usize) : U32 := queries.val.getD index.val 0#u32

theorem query_read (queries : Queries) (index : Usize) (bound : index.val<22) :
    Array.index_usize queries index=.ok (queryAt queries index) := by
  have hi : index.val<queries.val.length := by scalar_tac
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq,List.getElem?_eq_getElem hi]
  exact congrArg Result.ok (List.getD_eq_getElem queries.val 0#u32 hi).symm

def optimizedQuery {A T : Type} (queries : Queries) (folds index start : Usize)
    (cache : alloc.vec.Vec M) (before : Result (core.result.Result A verifier.Error))
    (tail : M→A→Result T) (error : verifier.Error→Result T) : Result T := do
  let query ← Array.index_usize queries index
  let u ← lift (UScalar.cast .Usize query)
  let result ← before
  match result with
  | .Err e => error e
  | .Ok value => do
    let node ← selected folds cache index start u
    tail node value

def referenceQuery {A T : Type} (queries : Queries) (folds index : Usize)
    (before : Result (core.result.Result A verifier.Error))
    (tail : M→A→Result T) (error : verifier.Error→Result T) : Result T := do
  let query ← Array.index_usize queries index
  let u ← lift (UScalar.cast .Usize query)
  let result ← before
  match result with
  | .Err e => error e
  | .Ok value => do
    let node ← old.node folds u
    tail node value

/-- All cache origin, length, checked query-read and subtraction obligations
follow from the actual builder success and actual caller reachability/guard.
No cache-lineage or candidate-equivalence premise is supplied. -/
theorem source_query_context {A T : Type} (queries : Queries)
    (folds index start finish : Usize) (front : new.Front)
    (built : new.front queries start finish=.ok (.Ok front))
    (calls : Calls start index) (guard : index<finish)
    (before : Result (core.result.Result A verifier.Error))
    (tail : M→A→Result T) (error : verifier.Error→Result T) :
    optimizedQuery queries folds index start front.line_z_values before tail error=
      referenceQuery queries folds index before tail error := by
  obtain ⟨hstart,hfinish,hlen,horigins⟩ := CuSavingsGeometryCache.source_success queries start finish front built
  have range := call_range calls guard
  have hb : index.val-start.val<front.line_z_values.val.length := by omega
  let query := queryAt queries index
  let z := front.line_z_values.val.getD (index.val-start.val) 0#u32
  have hz : front.line_z_values.val.getD (index.val-start.val) field.M31.ZERO=z := by
    simp only [field.M31.ZERO,z]
  have origin : Origin query z := by
    have h := horigins (index.val-start.val) hb
    have hsum : start.val+(index.val-start.val)=index.val := by omega
    simpa only [hsum,query,queryAt,z] using h
  have hnode := selected_equivalence folds front.line_z_values index start
    (UScalar.cast .Usize query) query z origin rfl range.1 hb hz
  unfold optimizedQuery referenceQuery
  rw [query_read queries index (by omega)]
  simp only [bind_tc_ok,lift]
  apply (bind_eq_iff before _ _).mpr
  intro result _
  cases result with
  | Err e => rfl
  | Ok value => rw [hnode]

/-- Full builder/inversion/query substitution in arbitrary common computational
contexts, preserving both source error channels and divergence. `prepare` is
the source-identical batch inversion tail on flat denominators and row count. -/
theorem source_caller_context {X A T : Type} (queries : Queries)
    (folds index start finish : Usize) (calls : Calls start index) (guard : index<finish)
    (prepare : Common→Result (core.result.Result X verifier.Error))
    (before : X→Result (core.result.Result A verifier.Error))
    (tail : M→A→Result T) (error : verifier.Error→Result T) :
    (do let result ← new.front queries start finish
        match result with
        | .Err e => error e
        | .Ok front => do
          let prepared ← prepare (newView front)
          match prepared with
          | .Err e => error e
          | .Ok value => optimizedQuery queries folds index start front.line_z_values (before value) tail error)=
    (do let result ← old.front queries start finish
        match result with
        | .Err e => error e
        | .Ok front => do
          let prepared ← prepare (oldView front)
          match prepared with
          | .Err e => error e
          | .Ok value => referenceQuery queries folds index (before value) tail error) := by
  let after : Common→Result T := fun common => do
    let prepared ← prepare common
    match prepared with
    | .Err e => error e
    | .Ok value => referenceQuery queries folds index (before value) tail error
  have replace :
      (do let result ← new.front queries start finish
          match result with
          | .Err e => error e
          | .Ok front => do
            let prepared ← prepare (newView front)
            match prepared with
            | .Err e => error e
            | .Ok value => optimizedQuery queries folds index start front.line_z_values (before value) tail error)=
      (do let result ← new.front queries start finish
          match result with | .Err e => error e | .Ok front => after (newView front)) := by
    apply (bind_eq_iff (new.front queries start finish) _ _).mpr
    intro result hbuild
    cases result with
    | Err e => rfl
    | Ok front =>
      apply (bind_eq_iff (prepare (newView front)) _ _).mpr
      intro prepared _
      cases prepared with
      | Err e => rfl
      | Ok value =>
        exact source_query_context queries folds index start finish front hbuild calls guard
          (before value) tail error
  have common := inversion_context queries start finish after error
  exact replace.trans common

#print axioms query_read
#print axioms source_query_context
#print axioms source_caller_context
end AspisR1.CuSavingsGeometryCandidate7
